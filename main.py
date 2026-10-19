# -*- coding: utf-8 -*-
"""status —— bot 运行状态查询（公开概览 + 管理员明细）。

设计要点
--------
* 只做手动查询，不轮询、不主动推送。
* 数据来源限定为：gatekeeper 的公开只读快照、框架本地状态、本进程指标。
  群列表优先复用 gatekeeper 最近一次完整结果；两边都没有才向 QQ 适配器请求 1 次。
* 权限先于取数：管理子指令在群内只提示私聊，普通用户不给跨群数据。
* 视图先按权限裁剪，再渲染图片；图片失败时用**同一视图**输出文字，两者信息一致。
* 不绕过 gatekeeper：群模式不放行时本插件的 handler 会被其运行时闸门剔除。
"""

from __future__ import annotations

import asyncio
import os
import time
import uuid
from collections import OrderedDict
from datetime import datetime
from zoneinfo import ZoneInfo

import psutil
from PIL import Image, ImageDraw

from astrbot.api import logger
from astrbot.api.event import filter
from astrbot.api.star import Context, Star
from astrbot.core.config.astrbot_config import AstrBotConfig
from astrbot.core.platform import AstrMessageEvent
from astrbot.core.star.filter.event_message_type import EventMessageType
from astrbot.core.star.session_llm_manager import SessionServiceManager
from astrbot.core.star.star_handler import star_map
from astrbot.core.utils.astrbot_path import get_astrbot_temp_path
from astrbot.core.utils.t2i.local_strategy import FontManager, TextMeasurer

PLUGIN_NAME = "status"
PLUGIN_DIR = "astrbot_plugin_status"
GATEKEEPER_NAME = "gatekeeper"

INVENTORY_TTL = 900.0          # 群列表缓存寿命（秒）
INVENTORY_TIMEOUT = 5.0        # 单次群列表请求超时
REQUEST_FAIL_COOLDOWN = 60.0   # 自动补拉抑制窗口
MANUAL_REFRESH_COOLDOWN = 60.0  # 手动刷新冷却（成功/失败都计）
CARD_TTL = 30.0                # 卡片图片复用
CARD_CACHE_MAX = 64
PAGE_SIZE = 10

TZ = ZoneInfo("Asia/Shanghai")

MODE_NAME = {"mute": "全禁", "llm": "只聊天", "plugin": "插件", "both": "全开"}
MODE_SUFFIX = {"mute": "全禁模式", "llm": "只聊天模式", "plugin": "插件模式", "both": "全开模式"}
KIND_NAME = {"personal": "个人禁言", "whole": "全体禁言"}
PHASE_NAME = {"known_ban": "禁言中", "recovery_wait": "恢复等待"}

# 浅色仪表盘配色（正常绿 / 限制橙 / 异常红 / 未知灰）
C_BG = (243, 244, 246)
C_CARD = (255, 255, 255)
C_LINE = (229, 231, 235)
C_TEXT = (17, 24, 39)
C_MUTED = (107, 114, 128)
C_OK = (21, 128, 61)
C_WARN = (194, 65, 12)
C_BAD = (185, 28, 28)
C_INFO = (29, 78, 216)

TONES = {
    "text": C_TEXT,
    "muted": C_MUTED,
    "ok": C_OK,
    "warn": C_WARN,
    "bad": C_BAD,
    "info": C_INFO,
}


class _Cooldown(Exception):
    """手动刷新冷却中。"""

    def __init__(self, seconds: int) -> None:
        super().__init__(f"冷却 {seconds}s")
        self.seconds = seconds


def _fmt_span(seconds: float) -> str:
    sec = int(max(0, seconds))
    days, rem = divmod(sec, 86400)
    hours, rem = divmod(rem, 3600)
    mins = rem // 60
    if days:
        return f"{days} 天 {hours} 小时" if hours else f"{days} 天"
    if hours:
        return f"{hours} 小时 {mins} 分" if mins else f"{hours} 小时"
    if mins:
        return f"{mins} 分钟"
    return "刚刚启动"


def _hm(ts) -> str:
    if not ts:
        return "—"
    try:
        return datetime.fromtimestamp(float(ts), TZ).strftime("%m-%d %H:%M")
    except (TypeError, ValueError, OSError):
        return "—"


def _hms(ts) -> str:
    if not ts:
        return "—"
    try:
        return datetime.fromtimestamp(float(ts), TZ).strftime("%m-%d %H:%M:%S")
    except (TypeError, ValueError, OSError):
        return "—"


def _brief(exc, limit: int = 80) -> str:
    text = str(exc).replace("\n", " ").strip() or exc.__class__.__name__
    return text[:limit]


def _kv_sections(block: dict) -> list[dict]:
    """kv 块可含多个小节（同一张卡内），也兼容单小节写法。"""
    if block.get("sections"):
        return block["sections"]
    return [{"title": block.get("title"), "items": block.get("items") or []}]


# --------------------------------------------------------------------------- #
# 仪表盘渲染（Pillow · 全本地资源，字体与换行复用框架 T2I 实现）
# --------------------------------------------------------------------------- #
class _Dashboard:
    W = 900
    SCALE = 2
    PAD = 26
    GAP = 14
    CARD_PAD = 20
    ROW_H = 34

    def __init__(self, view: dict) -> None:
        self.view = view
        self.s = self.SCALE
        self.img = Image.new("RGB", (self.W * self.s, 240 * self.s), C_BG)
        self.d = ImageDraw.Draw(self.img)
        self.y = self.PAD * self.s
        self.inner_w = (self.W - 2 * self.PAD - 2 * self.CARD_PAD) * self.s

    # ---- 基础度量 ----
    def _font(self, size: int, bold: bool = False):
        return FontManager.get_font(int(size * self.s), bold=bold)

    def _tw(self, text: str, font) -> int:
        return TextMeasurer.get_text_size(text, font)[0]

    def _lh(self, font) -> int:
        return TextMeasurer.get_text_size("Ag", font)[1]

    def _adv(self, font) -> int:
        return max(1, int(self._lh(font) * 1.45))

    def _wrap(self, text: str, font, width: int) -> list[str]:
        if width <= 8:
            return [self._clip(text, font, width)]
        return TextMeasurer.split_text_to_fit_width(text, font, width) or [""]

    def _clip(self, text: str, font, width: int) -> str:
        text = str(text)
        if width <= 8 or self._tw(text, font) <= width:
            return text
        low, high = 0, len(text)
        while low < high:
            mid = (low + high + 1) // 2
            if self._tw(text[:mid] + "…", font) <= width:
                low = mid
            else:
                high = mid - 1
        return text[:low] + "…"

    def _ensure(self, need_y: int) -> None:
        if need_y <= self.img.height:
            return
        height = max(need_y + 240 * self.s, int(self.img.height * 1.4))
        canvas = Image.new("RGB", (self.img.width, height), C_BG)
        canvas.paste(self.img, (0, 0))
        self.img = canvas
        self.d = ImageDraw.Draw(self.img)

    # ---- 块高度 ----
    def _kv_height(self, block: dict) -> int:
        font = self._font(15)
        adv = self._adv(font)
        value_w = self.inner_w - 150 * self.s
        title_h = self._lh(self._font(15, True)) + 10 * self.s
        total = 0
        for idx, section in enumerate(_kv_sections(block)):
            if idx:
                total += 16 * self.s
            if section.get("title"):
                total += title_h
            for i, (_label, value, _tone) in enumerate(section["items"]):
                if i:
                    total += 12 * self.s
                total += len(self._wrap(str(value), font, value_w)) * adv
        return total + 2 * self.CARD_PAD * self.s

    def _table_height(self, block: dict) -> int:
        total = 0
        if block.get("title"):
            total += self._lh(self._font(15, True)) + 10 * self.s
        font = self._font(14)
        total += self._adv(font) + 8 * self.s
        rows = block["rows"]
        if rows:
            total += len(rows) * self.ROW_H * self.s
        else:
            total += 2 * self._adv(font)
        return total + 2 * self.CARD_PAD * self.s

    def _note_height(self, block: dict) -> int:
        font = self._font(14)
        lines = self._wrap(block["text"], font, self.inner_w)
        return len(lines) * self._adv(font) + 2 * self.CARD_PAD * self.s

    def _height(self, block: dict) -> int:
        kind = block["type"]
        if kind == "kv":
            return self._kv_height(block)
        if kind == "table":
            return self._table_height(block)
        return self._note_height(block)

    # ---- 卡片 ----
    def _card(self, block: dict, draw_body) -> None:
        height = self._height(block)
        x0 = self.PAD * self.s
        x1 = (self.W - self.PAD) * self.s
        y0 = self.y
        self._ensure(y0 + height + self.GAP * self.s)
        self.d.rounded_rectangle(
            [x0, y0, x1, y0 + height],
            radius=14 * self.s,
            fill=C_CARD,
            outline=C_LINE,
            width=max(1, self.s),
        )
        draw_body(x0 + self.CARD_PAD * self.s, y0 + self.CARD_PAD * self.s)
        self.y = y0 + height + self.GAP * self.s

    # ---- 各块绘制 ----
    def _draw_kv(self, block: dict, x: int, y: int) -> None:
        font = self._font(15)
        title_font = self._font(15, True)
        adv = self._adv(font)
        label_w = 150 * self.s
        right = x + self.inner_w
        for idx, section in enumerate(_kv_sections(block)):
            if idx:
                y += 16 * self.s
            if section.get("title"):
                self.d.text((x, y), section["title"], font=title_font, fill=C_TEXT)
                y += self._lh(title_font) + 10 * self.s
            for i, (label, value, tone) in enumerate(section["items"]):
                if i:
                    y += 12 * self.s
                self.d.text((x, y), label, font=font, fill=C_MUTED)
                lines = self._wrap(str(value), font, right - (x + label_w))
                for j, line in enumerate(lines):
                    self.d.text(
                        (x + label_w, y + j * adv),
                        line,
                        font=font,
                        fill=TONES.get(tone, C_TEXT),
                    )
                y += len(lines) * adv

    def _cols(self, cols: list) -> list[tuple[int, int]]:
        weights = [max(1, int(w)) for _h, w in cols]
        total = sum(weights)
        start = (self.PAD + self.CARD_PAD) * self.s
        right = start + self.inner_w
        spans = []
        acc = 0
        prev = start
        for weight in weights:
            acc += weight
            end = start + int(self.inner_w * acc / total)
            spans.append((prev, end))
            prev = end
        spans[-1] = (spans[-1][0], right)
        return spans

    def _draw_table(self, block: dict, x: int, y: int) -> None:
        if block.get("title"):
            font = self._font(15, True)
            self.d.text((x, y), block["title"], font=font, fill=C_TEXT)
            y += self._lh(font) + 10 * self.s
        head_font = self._font(13)
        body_font = self._font(14)
        spans = self._cols(block["cols"])
        for (header, _w), (xs, xe) in zip(block["cols"], spans):
            self.d.text((xs, y), header, font=head_font, fill=C_MUTED)
        y += self._adv(head_font)
        self.d.line(
            [(x, y), (x + self.inner_w, y)], fill=C_LINE, width=max(1, self.s // 2)
        )
        y += 8 * self.s

        rows = block["rows"]
        if not rows:
            self.d.text((x, y), block.get("empty") or "（无记录）", font=body_font, fill=C_MUTED)
            return
        line_h = self._lh(body_font)
        for row in rows:
            center_y = y + (self.ROW_H * self.s - line_h) // 2
            last = len(spans) - 1
            for idx, ((text, tone), (xs, xe)) in enumerate(zip(row, spans)):
                cell = str(text)
                width = xe - xs - 12 * self.s
                cell = self._clip(cell, body_font, width)
                if idx == last:
                    self.d.text(
                        (xe - self._tw(cell, body_font), center_y),
                        cell,
                        font=body_font,
                        fill=TONES.get(tone, C_TEXT),
                    )
                else:
                    self.d.text(
                        (xs, center_y), cell, font=body_font, fill=TONES.get(tone, C_TEXT)
                    )
            y += self.ROW_H * self.s

    def _draw_note(self, block: dict, x: int, y: int) -> None:
        font = self._font(14)
        adv = self._adv(font)
        for i, line in enumerate(self._wrap(block["text"], font, self.inner_w)):
            self.d.text((x, y + i * adv), line, font=font, fill=TONES.get(block.get("tone"), C_MUTED))

    # ---- 组装 ----
    def build(self) -> Image.Image:
        title_font = self._font(25, True)
        sub_font = self._font(14)

        if self.view.get("title"):
            self.d.text(
                (self.PAD * self.s, self.y), self.view["title"], font=title_font, fill=C_TEXT
            )
            self.y += self._lh(title_font) + 6 * self.s
        if self.view.get("subtitle"):
            self.d.text(
                (self.PAD * self.s, self.y),
                self.view["subtitle"],
                font=sub_font,
                fill=C_MUTED,
            )
            self.y += self._lh(sub_font)
        self.y += 14 * self.s

        for block in self.view.get("blocks") or []:
            if block["type"] == "kv":
                self._card(block, lambda x, y, b=block: self._draw_kv(b, x, y))
            elif block["type"] == "table":
                self._card(block, lambda x, y, b=block: self._draw_table(b, x, y))
            else:
                self._card(block, lambda x, y, b=block: self._draw_note(b, x, y))

        footer = self.view.get("footer")
        if footer:
            self._ensure(self.y + 60 * self.s)
            font = self._font(13)
            self.d.text(
                (self.PAD * self.s, self.y), footer, font=font, fill=C_MUTED
            )
            self.y += self._lh(font)
        self.y += self.PAD * self.s
        self._ensure(self.y)
        return self.img.crop((0, 0, self.img.width, max(1, self.y)))


# --------------------------------------------------------------------------- #
# 插件
# --------------------------------------------------------------------------- #
class StatusPlugin(Star):
    def __init__(self, context: Context, config: AstrBotConfig | None = None):
        super().__init__(context)
        self.config = config if isinstance(config, dict) else {}
        self._proc = psutil.Process(os.getpid())

        # 群列表缓存（单调时钟判定寿命）
        self._inv: dict | None = None
        self._inv_mono = 0.0
        self._inv_dirty = False
        self._inv_dirty_at = 0.0  # 最近一次成员变动时间（墙钟），用于拒收更早采集的快照
        self._inv_task: asyncio.Task | None = None
        self._fail_mono: float | None = None
        self._fail_reason = ""
        self._refresh_mono: float | None = None

        # 卡片图片复用
        self._cards: OrderedDict[str, tuple[float, str]] = OrderedDict()
        # CPU 采样（上次样本，不额外起定时采样）
        self._cpu_prev: tuple[float, float] | None = None

        logger.info("[status] 已加载。群列表 TTL=%ss，卡片复用=%ss。", INVENTORY_TTL, CARD_TTL)

    # ===================== 集成入口 =====================
    def _gatekeeper(self) -> tuple[object | None, str]:
        """每次查询重新取当前实例，不永久持有已卸载的 gatekeeper。"""
        meta = None
        for item in list(star_map.values()):
            if getattr(item, "name", None) == GATEKEEPER_NAME:
                meta = item
                break
        if meta is None:
            return None, "未安装 gatekeeper 插件"
        if not bool(getattr(meta, "activated", True)):
            # 面板停用后框架保留 star_cls，实例仍可调用；必须显式看激活状态
            return None, "gatekeeper 已被停用"
        inst = getattr(meta, "star_cls", None)
        if inst is None:
            return None, "gatekeeper 未加载"
        if not callable(getattr(inst, "get_status_snapshot", None)):
            return None, "gatekeeper 版本不支持状态快照（需 0.4.0+）"
        return inst, ""

    def _snapshot(self) -> tuple[dict | None, str]:
        inst, reason = self._gatekeeper()
        if inst is None:
            return None, reason
        try:
            snap = inst.get_status_snapshot()
        except Exception as exc:
            logger.error("[status] 读取 gatekeeper 快照失败：%s", _brief(exc, 200))
            return None, f"gatekeeper 快照读取失败：{_brief(exc)}"
        if not isinstance(snap, dict) or not isinstance(snap.get("groups"), list):
            logger.error("[status] gatekeeper 快照结构不符合约定：%r", type(snap))
            return None, "gatekeeper 快照结构不符合约定"
        return snap, ""

    # ===================== 群列表 =====================
    def _cached_fresh(self) -> bool:
        return (
            self._inv is not None
            and self._inv.get("groups") is not None
            and not self._inv_dirty
            and (time.monotonic() - self._inv_mono) < INVENTORY_TTL
        )

    def _store_inv(self, groups: dict, observed_at: float, source: str, self_id: str = "") -> None:
        age = max(0.0, time.time() - float(observed_at))
        self._inv_mono = time.monotonic() - age  # 按原始观测时间计时，导入不重新计时
        self._inv = {
            "groups": groups,
            "observed_at": float(observed_at),
            "source": source,
            "self_id": self_id,
            "stale": False,
            "error": None,
        }
        self._inv_dirty = False
        self._inv_dirty_at = 0.0

    def _stale_inv(self, reason: str) -> dict:
        if self._inv is not None and self._inv.get("groups") is not None:
            out = dict(self._inv)
            out["stale"] = True
            out["error"] = reason
            return out
        return {
            "groups": None,
            "observed_at": 0.0,
            "source": "",
            "self_id": "",
            "stale": True,
            "error": reason,
        }

    def _import_from_gatekeeper(self, snap: dict | None, self_id: str) -> dict | None:
        if not snap:
            return None
        inv = snap.get("inventory") or {}
        groups = inv.get("groups")
        observed = inv.get("observed_at")
        if not isinstance(groups, dict) or not groups or not observed:
            return None
        owner = str(inv.get("self_id") or "")
        if self_id and owner and owner != self_id:
            return None  # 不是同一个号的数据，不合并
        observed = float(observed)
        age = time.time() - observed
        payload = {str(k): str(v or "") for k, v in groups.items()}
        if self._inv_dirty and observed <= self._inv_dirty_at:
            # 快照采集于最近一次加退群之前，不能代表变动后的成员关系，也不清失效标记
            return None
        if 0 <= age <= INVENTORY_TTL:
            self._store_inv(payload, observed, "gatekeeper", owner)
            return self._inv
        return None

    def _cached_inv(self) -> dict:
        """只读本地已有缓存，不触发任何请求（plugins / runtime 用）。"""
        if self._inv is not None and self._inv.get("groups") is not None:
            return dict(self._inv)
        return {
            "groups": None,
            "observed_at": 0.0,
            "source": "",
            "self_id": "",
            "stale": False,
            "error": None,
        }

    async def _inventory(self, event: AstrMessageEvent, *, snap: dict | None = None,
                         manual: bool = False) -> dict:
        self_id = str(event.get_self_id() or "")

        if not manual and self._cached_fresh():
            return self._inv

        if not manual:
            imported = self._import_from_gatekeeper(snap, self_id)
            if imported is not None:
                return imported

        return await self._request_inventory(event, self_id, manual=manual)

    async def _request_inventory(self, event: AstrMessageEvent, self_id: str,
                                 *, manual: bool = False) -> dict:
        now = time.monotonic()

        if manual and self._refresh_mono is not None:
            left = MANUAL_REFRESH_COOLDOWN - (now - self._refresh_mono)
            if left > 0:
                raise _Cooldown(max(1, int(left) + 1))

        running = self._inv_task
        if running is not None and not running.done():
            # 与自动补拉共用同一次请求，但手动刷新同样要消耗冷却
            try:
                return await running
            finally:
                if manual:
                    self._refresh_mono = time.monotonic()

        if (
            not manual
            and self._fail_mono is not None
            and (now - self._fail_mono) < REQUEST_FAIL_COOLDOWN
        ):
            left = int(REQUEST_FAIL_COOLDOWN - (now - self._fail_mono)) + 1
            return self._stale_inv(f"{self._fail_reason or '上次请求失败'}（{left} 秒内不重复请求）")

        task = asyncio.get_running_loop().create_task(self._do_request(event, self_id))
        self._inv_task = task
        try:
            return await task
        finally:
            if self._inv_task is task:
                self._inv_task = None
            if manual:
                self._refresh_mono = time.monotonic()  # 失败同样消耗冷却

    async def _do_request(self, event: AstrMessageEvent, self_id: str) -> dict:
        plat, err = self._target_platform()
        if plat is None:
            self._fail_mono = time.monotonic()
            self._fail_reason = err
            return self._stale_inv(err)
        try:
            rows = await asyncio.wait_for(
                plat.get_client().get_group_list(), timeout=INVENTORY_TIMEOUT
            )
            groups = self._parse_rows(rows)
        except Exception as exc:
            self._fail_mono = time.monotonic()
            self._fail_reason = _brief(exc)
            logger.warning("[status] 群列表请求失败：%s", self._fail_reason)
            return self._stale_inv(self._fail_reason)
        self._fail_mono = None
        self._fail_reason = ""
        self._store_inv(groups, time.time(), "adapter", self_id)
        return self._inv

    @staticmethod
    def _parse_rows(rows) -> dict:
        if not isinstance(rows, list):
            raise ValueError("群列表格式非法")
        groups: dict[str, str] = {}
        for row in rows:
            if not isinstance(row, dict):
                raise ValueError("群列表格式非法")
            gid = str(row.get("group_id") or "")
            if not gid.isdigit():
                raise ValueError("群列表格式非法")
            groups[gid] = str(row.get("group_name") or "")
        return groups

    def _target_platform(self) -> tuple[object | None, str]:
        mgr = getattr(self.context, "platform_manager", None)
        insts = []
        for plat in getattr(mgr, "platform_insts", []) or []:
            try:
                if plat.meta().name == "aiocqhttp":
                    insts.append(plat)
            except Exception:
                continue
        if not insts:
            return None, "未找到 QQ 适配器（aiocqhttp）"
        if len(insts) == 1:
            return insts[0], ""
        want = str(self.config.get("target_platform_id") or "").strip()
        if want:
            for plat in insts:
                try:
                    if plat.meta().id == want:
                        return plat, ""
                except Exception:
                    continue
            return None, f"配置的 target_platform_id={want} 未匹配到已连接账号"
        return None, "检测到多个 QQ 账号，请在本插件配置中设置 target_platform_id"

    # ===================== 运行指标 =====================
    def _connection(self, event: AstrMessageEvent) -> tuple[str, str]:
        plat, _err = self._target_platform()
        if plat is None:
            return "未知", "muted"
        try:
            value = getattr(plat.status, "value", "")
        except Exception:
            return "未知", "muted"
        if value == "running":
            return "已连接", "ok"
        if value == "error":
            return "未连接（异常）", "bad"
        if value == "stopped":
            return "未连接", "bad"
        return "未知", "muted"

    def _uptime(self) -> str:
        try:
            started = float(self._proc.create_time())
        except Exception:
            return "未知"
        return f"{_fmt_span(time.time() - started)} · 后端运行"

    def _cpu(self) -> tuple[str, str]:
        try:
            times = self._proc.cpu_times()
            total = float(times.user) + float(times.system)
        except Exception:
            return "未知", "muted"
        now = time.monotonic()
        prev = self._cpu_prev
        self._cpu_prev = (now, total)
        if prev is None:
            return "采样中", "muted"
        span = now - prev[0]
        if span <= 0.2:
            return "采样中", "muted"
        cores = psutil.cpu_count(logical=True) or 1
        pct = max(0.0, min(100.0, (total - prev[1]) / span / cores * 100.0))
        return f"{pct:.1f}%（按 {cores} 逻辑核归一）", "text"

    def _memory(self) -> str:
        try:
            rss = float(self._proc.memory_info().rss)
        except Exception:
            return "未知"
        return f"{rss / (1024 * 1024):.0f} MiB"

    def _plugin_rows(self) -> list[dict]:
        failed = getattr(getattr(self.context, "_star_manager", None), "failed_plugin_dict", None)
        failed = failed if isinstance(failed, dict) else {}
        rows = []
        seen_dirs: set[str] = set()
        for meta in list(star_map.values()):
            name = getattr(meta, "name", None)
            if not name or getattr(meta, "reserved", False) or name == PLUGIN_NAME:
                continue
            root = str(getattr(meta, "root_dir_name", None) or "")
            if root:
                seen_dirs.add(root)
            rows.append(
                {
                    "id": str(name),
                    "display": str(getattr(meta, "display_name", None) or name),
                    "version": str(getattr(meta, "version", None) or ""),
                    "loaded": getattr(meta, "star_cls", None) is not None,
                    "enabled": bool(getattr(meta, "activated", True)),
                    "failed": root in failed,
                }
            )
        # 加载失败的插件已被框架从 star_map 清理，必须单独并入失败记录才能看见
        seen_ids = {r["id"] for r in rows}
        for dir_name, info in failed.items():
            dir_key = str(dir_name or "")
            if not dir_key or dir_key in seen_dirs or dir_key == PLUGIN_DIR:
                continue
            info = info if isinstance(info, dict) else {}
            if info.get("reserved"):
                continue
            name = str(info.get("name") or dir_key)
            if name == PLUGIN_NAME or name in seen_ids:
                continue
            seen_ids.add(name)
            rows.append(
                {
                    "id": name,
                    "display": str(info.get("display_name") or name),
                    "version": str(info.get("version") or ""),
                    "loaded": False,
                    "enabled": False,
                    "failed": True,
                }
            )
        rows.sort(key=lambda r: (not r["enabled"], r["id"].lower(), r["id"]))
        return rows

    def _plugin_state(self, row: dict) -> tuple[str, str]:
        if row["failed"]:
            return "加载失败", "bad"
        if not row["loaded"]:
            return "未加载", "warn"
        if not row["enabled"]:
            return "已停用", "muted"
        return "已启用", "ok"

    # ===================== 视图：概览 =====================
    def _bot_name(self, event: AstrMessageEvent) -> str:
        try:
            plat, _err = self._target_platform()
            if plat is not None:
                return str(plat.meta().id)
        except Exception:
            pass
        return "Bot"

    @staticmethod
    def _entry(snap: dict | None, gid: str) -> dict | None:
        for item in (snap or {}).get("groups") or []:
            if str(item.get("group_id")) == str(gid):
                return item
        return None

    def _restriction_counts(self, snap: dict | None, inv: dict) -> dict:
        dash = {"known": "—", "known_tone": "muted", "wait": "—", "wait_tone": "muted",
                "why": ""}
        if snap is None:
            dash["why"] = "gatekeeper 不可用，限制数据未知"
            return dash
        if not snap.get("enabled"):
            dash["why"] = "gatekeeper 总控已关闭"
            return dash
        joined = inv.get("groups")
        if joined is None:
            dash["why"] = "群列表未知，无法给出已加入群范围统计"
            return dash
        known = wait = 0
        for item in snap.get("groups") or []:
            if str(item.get("group_id")) not in joined:
                continue
            phase = item.get("restriction_phase")
            if phase == "known_ban":
                known += 1
            elif phase == "recovery_wait":
                wait += 1
        return {
            "known": f"{known} 群",
            "known_tone": "warn" if known else "text",
            "wait": f"{wait} 群",
            "wait_tone": "warn" if wait else "text",
            "why": "",
        }

    @staticmethod
    def _mode_text(mode) -> str:
        if mode is None:
            return "未知"
        if mode == "off":
            return "不接管"
        return MODE_SUFFIX.get(str(mode), str(mode))

    @staticmethod
    def _policy_flags(mode, snap: dict | None) -> tuple[tuple[str, str], tuple[str, str]]:
        if mode is None:
            unknown = ("未知", "muted")
            return unknown, unknown
        if mode == "off":
            off = ("不接管", "muted")
            return off, off
        opts = (snap or {}).get("policy_options") or {}
        plugins_ok = mode in ("plugin", "both")
        llm_ok = mode in ("llm", "both")
        plugin_item = ("策略允许", "ok") if plugins_ok else ("策略禁止", "warn")
        if llm_ok:
            prob = opts.get("probability")
            if isinstance(prob, (int, float)) and 0 <= float(prob) < 100:
                llm_item = (f"策略允许 · 概率 {float(prob):g}%", "warn")
            else:
                llm_item = ("策略允许", "ok")
        else:
            llm_item = ("策略禁止", "warn")
        return plugin_item, llm_item

    def _restriction_line(self, entry: dict | None) -> tuple[str, str]:
        if entry is None:
            return "尚无检测记录", "muted"
        phase = entry.get("restriction_phase")
        kind = entry.get("restriction_kind")
        if phase == "recovery_wait":
            return "预计禁言已到期，策略等待恢复", "warn"
        if phase == "known_ban":
            if kind == "whole":
                return "全体禁言中（无固定解除时间）", "bad"
            return f"个人禁言中，预计 {_hm(entry.get('expected_ban_end_at'))} 结束", "bad"
        if entry.get("observation") == "clear":
            return f"上次检查未发现禁言（{_hm(entry.get('last_observed_at'))}）", "ok"
        return "尚无检测记录", "muted"

    def _view_overview(self, event: AstrMessageEvent, *, snap, snap_err: str,
                       inv: dict, admin: bool) -> dict:
        gid = str(event.get_group_id() or "")
        is_group = bool(gid)
        conn_text, conn_tone = self._connection(event)

        joined = inv.get("groups")
        cache_tag = "（缓存）" if inv.get("stale") else ""
        if joined is None:
            group_text, group_tone = "未知", "muted"
        else:
            group_text, group_tone = f"{len(joined)} 群{cache_tag}", "text"

        counts = self._restriction_counts(snap, inv)

        blocks = [
            {
                "type": "kv",
                "sections": [
                    {
                        "title": "运行",
                        "items": [
                            ("连接", conn_text, conn_tone),
                            ("运行", self._uptime(), "muted"),
                        ],
                    },
                    {
                        "title": "群聊",
                        "items": [("已加入群聊", group_text, group_tone)],
                    },
                    {
                        "title": "限制",
                        "items": [
                            ("已知禁言记录", counts["known"], counts["known_tone"]),
                            ("恢复等待", counts["wait"], counts["wait_tone"]),
                        ],
                    },
                ],
            },
        ]

        if is_group:
            entry = self._entry(snap, gid)
            # 本群未被快照收录时，模式按默认模式解释（总控关闭则为 off）
            mode = entry.get("effective_mode") if entry else self._default_mode(snap)
            plugin_item, llm_item = self._policy_flags(mode, snap)
            restriction, restriction_tone = self._restriction_line(entry)
            blocks.append(
                {
                    "type": "kv",
                    "title": "当前群",
                    "items": [
                        ("群模式", self._mode_text(mode), "text" if mode else "muted"),
                        ("插件", plugin_item[0], plugin_item[1]),
                        ("默认聊天", llm_item[0], llm_item[1]),
                        ("QQ 限制", restriction, restriction_tone),
                    ],
                }
            )

        if admin and not is_group:
            if snap is None:
                gate_text, gate_tone = "不可用", "muted"
            elif not snap.get("enabled"):
                gate_text, gate_tone = "已关闭（不接管）", "warn"
            else:
                gate_text, gate_tone = "接管中", "ok"
            rows = self._plugin_rows()
            loaded = sum(1 for r in rows if r["loaded"])
            enabled = sum(1 for r in rows if r["enabled"])
            cpu_text, cpu_tone = self._cpu()
            blocks.append(
                {
                    "type": "kv",
                    "title": "管理",
                    "items": [
                        ("总控", gate_text, gate_tone),
                        ("插件", f"{loaded} 已加载 / {enabled} 已启用", "text"),
                        ("进程 CPU", cpu_text, cpu_tone),
                        ("进程内存", self._memory(), "text"),
                    ],
                }
            )

        if counts["why"]:
            blocks.append({"type": "note", "text": counts["why"], "tone": "muted"})
        if snap_err:
            blocks.append({"type": "note", "text": snap_err, "tone": "muted"})

        now = _hm(time.time())
        footer = f"数据时间 {now}"
        if admin and not is_group:
            footer += " · groups · bans · plugins · runtime"
        elif not admin:
            footer += " · 发送 /status help 查看用法"

        return {
            "title": f"{self._bot_name(event)} · 状态",
            "subtitle": None,
            "blocks": blocks,
            "footer": footer,
        }

    # ===================== 视图：列表 =====================
    @staticmethod
    def _default_mode(snap: dict | None):
        """快照存在时，未单独配置的群等于默认模式；总控关闭则一律不接管。"""
        if snap is None:
            return None
        return snap.get("default_mode") if snap.get("enabled") else "off"

    def _group_rows(self, snap: dict | None, inv: dict) -> list[dict]:
        """成员列表为主表，gatekeeper 快照只负责补策略。

        新群尚无快照记录时，模式按默认模式解释，限制状态记为空（未知），
        不能当成「已检查且正常」。群名优先取更新的成员列表。
        """
        joined = inv.get("groups")
        entries: dict[str, dict] = {}
        for item in (snap or {}).get("groups") or []:
            key = str(item.get("group_id"))
            if key:
                entries[key] = item
        default_mode = self._default_mode(snap)
        rows = []
        if joined is not None:
            for gid, name in joined.items():
                gid = str(gid)
                entry = entries.get(gid) or {}
                rows.append(
                    {
                        "gid": gid,
                        "name": str(name or entry.get("name") or ""),
                        "mode": entry.get("effective_mode") if entry else default_mode,
                        "configured_mode": entry.get("configured_mode") if entry else default_mode,
                        "phase": entry.get("restriction_phase") or "",
                        "kind": entry.get("restriction_kind") or "",
                        "release_at": entry.get("release_at"),
                        "tracked": bool(entry),
                        "joined": True,
                    }
                )
        else:
            for gid, entry in entries.items():
                rows.append(
                    {
                        "gid": gid,
                        "name": str(entry.get("name") or ""),
                        "mode": entry.get("effective_mode"),
                        "configured_mode": entry.get("configured_mode"),
                        "phase": entry.get("restriction_phase") or "",
                        "kind": entry.get("restriction_kind") or "",
                        "release_at": entry.get("release_at"),
                        "tracked": True,
                        "joined": None,
                    }
                )
        rows.sort(key=lambda r: int(r["gid"]) if r["gid"].isdigit() else 0)
        return rows

    @staticmethod
    def _bans_sort_key(row: dict):
        release = row.get("release_at")
        head = 0 if release is None else 1
        gid = int(row["gid"]) if str(row["gid"]).isdigit() else 0
        return (head, float(release or 0), gid)

    def _view_groups(self, snap, snap_err: str, inv: dict, page_arg: str) -> dict:
        rows = self._group_rows(snap, inv)
        if inv.get("groups") is None:
            verified = "成员关系未核验"
        else:
            verified = f"群列表 {_hm(inv.get('observed_at'))} 更新"
        untracked = sum(1 for r in rows if not r["tracked"])
        page = self._paginate(rows, page_arg)
        if isinstance(page, str):
            return self._error_view("群列表", page)

        number, pages, chunk = page
        out = []
        for row in chunk:
            phase = PHASE_NAME.get(row["phase"], "无记录")
            tone = "warn" if row["phase"] == "recovery_wait" else (
                "bad" if row["phase"] == "known_ban" else "muted")
            out.append(
                [
                    (row["name"] or "（未知群名）", "text"),
                    (row["gid"], "muted"),
                    (MODE_NAME.get(str(row["mode"]), self._mode_text(row["mode"])),
                     "text" if row["tracked"] else "muted"),
                    (phase, tone),
                ]
            )
        blocks = [
            {
                "type": "table",
                "title": None,
                "cols": [("群名", 40), ("群 ID", 24), ("模式", 18), ("限制", 18)],
                "rows": out,
                "empty": "当前没有已加入的群。",
            }
        ]
        if snap is None and inv.get("groups") is None:
            blocks = [
                {
                    "type": "note",
                    "text": snap_err or "群列表与 gatekeeper 数据均不可用，群数未知（不是 0）。",
                    "tone": "warn",
                }
            ]
        elif untracked and snap is not None:
            mode_text = self._mode_text(self._default_mode(snap))
            blocks.append(
                {
                    "type": "note",
                    "text": f"{untracked} 个群尚无 gatekeeper 记录：模式按默认（{mode_text}）"
                    "解释，限制状态未知，不代表已检查正常。",
                    "tone": "muted",
                }
            )
        return {
            "title": "群列表",
            "subtitle": f"共 {len(rows)} 群 · 第 {number}/{pages} 页 · {verified}",
            "blocks": blocks,
            "footer": f"数据时间 {_hm(time.time())}"
            + ("" if not snap_err else f" · {snap_err}"),
        }

    def _view_bans(self, snap, snap_err: str, inv: dict, page_arg: str) -> dict:
        if snap is None:
            # 没有快照时禁言记录是「未知」，不能渲染成 0 条
            return {
                "title": "禁言记录",
                "subtitle": None,
                "blocks": [
                    {
                        "type": "note",
                        "text": (snap_err or "gatekeeper 不可用")
                        + "\n没有 gatekeeper 数据，禁言记录未知（不是 0 条）。",
                        "tone": "warn",
                    }
                ],
                "footer": f"数据时间 {_hm(time.time())}",
            }
        if not snap.get("enabled"):
            return {
                "title": "禁言记录",
                "subtitle": None,
                "blocks": [
                    {
                        "type": "note",
                        "text": "gatekeeper 总控已关闭，当前不接管任何群；"
                        "历史禁言记录不作为当前生效限制。",
                        "tone": "warn",
                    }
                ],
                "footer": f"数据时间 {_hm(time.time())}",
            }
        rows = [
            r
            for r in self._group_rows(snap, inv)
            if r["phase"] in ("known_ban", "recovery_wait")
        ]
        rows.sort(key=self._bans_sort_key)

        page = self._paginate(rows, page_arg)
        if isinstance(page, str):
            return self._error_view("禁言记录", page)

        number, pages, chunk = page
        out = []
        for row in chunk:
            release = row.get("release_at")
            if row["phase"] == "recovery_wait":
                when = "已到期，等待策略恢复"
                tone = "warn"
            elif release is None:
                when = "无固定解除时间"
                tone = "bad"
            else:
                when = f"预计 {_hm(release)} 释放"
                tone = "bad"
            out.append(
                [
                    (row["name"] or "（未知群名）", "text"),
                    (row["gid"], "muted"),
                    (KIND_NAME.get(row["kind"], row["kind"] or "未知"), "text"),
                    (when, tone),
                ]
            )
        scope = "已加入群范围" if inv.get("groups") is not None else "成员关系未核验"
        if inv.get("stale"):
            scope += "（群列表为缓存）"
        listed = _hm(inv.get("observed_at")) if inv.get("groups") is not None else "—"
        return {
            "title": "禁言记录",
            "subtitle": f"共 {len(rows)} 条 · 第 {number}/{pages} 页 · {scope}",
            "blocks": [
                {
                    "type": "table",
                    "title": None,
                    "cols": [("群名", 32), ("群 ID", 22), ("类型", 20), ("状态", 26)],
                    "rows": out,
                    "empty": "没有已知禁言或恢复等待记录。",
                }
            ],
            "footer": f"数据时间 {_hm(time.time())} · 群列表 {listed} · "
            "来自 gatekeeper 记录，非实时核验",
        }

    def _view_plugins(self, page_arg: str) -> dict:
        rows = self._plugin_rows()
        page = self._paginate(rows, page_arg)
        if isinstance(page, str):
            return self._error_view("插件列表", page)
        number, pages, chunk = page
        out = []
        for row in chunk:
            state, tone = self._plugin_state(row)
            out.append(
                [
                    (row["id"], "text"),
                    (row["display"], "text"),
                    (row["version"] or "未声明", "muted"),
                    (state, tone),
                ]
            )
        loaded = sum(1 for r in rows if r["loaded"])
        enabled = sum(1 for r in rows if r["enabled"])
        failed = sum(1 for r in rows if r["failed"])
        subtitle = f"共 {len(rows)} 个 · 已加载 {loaded} / 已启用 {enabled}"
        if failed:
            subtitle += f" · 加载失败 {failed}"
        return {
            "title": "插件列表",
            "subtitle": f"{subtitle} · 第 {number}/{pages} 页",
            "blocks": [
                {
                    "type": "table",
                    "title": None,
                    "cols": [("插件标识", 34), ("显示名", 28), ("版本", 18), ("状态", 20)],
                    "rows": out,
                    "empty": "没有可列出的插件。",
                }
            ],
            "footer": "全局启用不等于任意群可用 · 单群禁用请查 /status group",
        }

    def _view_runtime(self, event: AstrMessageEvent, snap, snap_err: str, inv: dict) -> dict:
        conn_text, conn_tone = self._connection(event)
        joined = inv.get("groups")
        source = {"adapter": "QQ 适配器", "gatekeeper": "gatekeeper 快照"}.get(
            str(inv.get("source") or ""), "—"
        )
        if joined is None:
            if inv.get("error"):
                inv_text, inv_tone = "未知（上次请求失败）", "warn"
            else:
                inv_text, inv_tone = "尚未获取（可用 /status refresh 更新）", "muted"
        else:
            tag = "（缓存）" if inv.get("stale") else ""
            inv_text = f"{len(joined)} 群{tag} · {source} · {_hms(inv.get('observed_at'))}"
            inv_tone = "warn" if inv.get("stale") else "text"

        last = (snap or {}).get("last_scan") or {}
        if last:
            scan_text = (
                f"{_hms(last.get('finished_at'))} · 目标 {last.get('target')} / "
                f"成功 {last.get('ok')} / 失败 {last.get('failed')}"
                + ("（完整）" if last.get("complete") else "（不完整）")
            )
            scan_tone = "text" if last.get("complete") else "warn"
        else:
            scan_text, scan_tone = "尚无检测记录", "muted"

        if snap is None:
            gate_text, gate_tone = "不可用", "muted"
        elif snap.get("enabled"):
            gate_text, gate_tone = f"接管中 · 快照 {_hms(snap.get('captured_at'))}", "ok"
        else:
            gate_text, gate_tone = "已关闭（不接管）", "warn"

        rows = self._plugin_rows()
        loaded = sum(1 for r in rows if r["loaded"])
        enabled = sum(1 for r in rows if r["enabled"])
        cpu_text, cpu_tone = self._cpu()

        blocks = [
            {
                "type": "kv",
                "title": "运行",
                "items": [
                    ("连接", conn_text, conn_tone),
                    ("运行时长", self._uptime(), "muted"),
                    ("进程 CPU", cpu_text, cpu_tone),
                    ("进程内存", self._memory(), "text"),
                ],
            },
            {
                "type": "kv",
                "title": "数据来源",
                "items": [
                    ("群列表", inv_text, inv_tone),
                    ("禁言采集", scan_text, scan_tone),
                    ("gatekeeper", gate_text, gate_tone),
                ],
            },
            {
                "type": "kv",
                "title": "插件",
                "items": [("统计", f"{len(rows)} 个 · 已加载 {loaded} · 已启用 {enabled}", "text")],
            },
        ]
        if inv.get("error"):
            blocks.append(
                {"type": "note", "text": f"群列表刷新失败：{inv['error']}", "tone": "warn"}
            )
        if snap_err:
            blocks.append({"type": "note", "text": snap_err, "tone": "muted"})
        return {
            "title": "运行详情",
            "subtitle": None,
            "blocks": blocks,
            "footer": f"数据时间 {_hm(time.time())} · 时间为 Asia/Shanghai",
        }

    # ===================== 视图：单群详情 =====================
    async def _session_switches(self, event: AstrMessageEvent, gid: str) -> dict | None:
        try:
            platform_id = str(event.unified_msg_origin).split(":")[0]
        except Exception:
            return None
        if not platform_id:
            return None
        umo = f"{platform_id}:GroupMessage:{gid}"
        try:
            return {
                "session": await SessionServiceManager.is_session_enabled(umo),
                "llm": await SessionServiceManager.is_llm_enabled_for_session(umo),
            }
        except Exception as exc:
            logger.warning("[status] 读取框架会话开关失败(%s)：%s", gid, _brief(exc))
            return None

    async def _view_group(self, event: AstrMessageEvent, snap, snap_err: str,
                          inv: dict, raw_gid: str) -> dict:
        gid = str(int(raw_gid))
        if snap is None and inv.get("groups") is None:
            return self._error_view("单群详情", snap_err or "gatekeeper 与群列表均不可用")

        entry = self._entry(snap, gid)
        joined = inv.get("groups")
        if joined is None:
            listed, listed_tone = "列表未知", "muted"
        elif gid in joined:
            listed, listed_tone = "在群列表中", "ok"
        else:
            listed, listed_tone = "未找到", "warn"

        name = (joined or {}).get(gid) or (entry or {}).get("name") or "（未知）"
        inferred = entry is None and joined is not None and gid in joined
        if entry is not None:
            mode = entry.get("effective_mode")
            configured = entry.get("configured_mode")
        elif inferred:
            # 成员列表里有、快照还没收录：模式等于默认模式，限制状态未知
            mode = configured = self._default_mode(snap)
        else:
            mode = configured = None
        phase = (entry or {}).get("restriction_phase") or ""
        kind = (entry or {}).get("restriction_kind") or ""

        restriction, restriction_tone = self._restriction_line(entry)
        if phase == "known_ban" or phase == "recovery_wait":
            restriction = f"{KIND_NAME.get(kind, kind)} · {PHASE_NAME.get(phase, phase)}"

        items = [
            ("群名", name, "text"),
            ("群 ID", gid, "muted"),
            ("群列表", listed, listed_tone),
            ("配置模式", self._mode_text(configured), "text"),
            ("生效模式", self._mode_text(mode), "text"),
            ("限制", restriction, restriction_tone),
            ("预计禁言结束", _hm((entry or {}).get("expected_ban_end_at")), "muted"),
            ("策略释放时间", _hm((entry or {}).get("release_at")), "muted"),
            ("最近成功观测", _hms((entry or {}).get("last_observed_at")), "muted"),
        ]
        off = (entry or {}).get("manual_off_plugins") or []
        items.append(("单群禁用插件", "、".join(off) if off else "无", "text" if off else "muted"))

        plugin_item, llm_item = self._policy_flags(mode, snap)
        policy_items = [
            ("插件大类", plugin_item[0], plugin_item[1]),
            ("默认聊天", llm_item[0], llm_item[1]),
        ]
        switches = await self._session_switches(event, gid)
        if switches is None:
            policy_items.append(("框架会话", "读取失败", "muted"))
        else:
            policy_items.append(
                ("框架会话", "已启用" if switches["session"] else "已停用",
                 "ok" if switches["session"] else "warn")
            )
            policy_items.append(
                ("框架聊天", "已启用" if switches["llm"] else "已停用",
                 "ok" if switches["llm"] else "warn")
            )

        blocks = [
            {"type": "kv", "title": "群信息", "items": items},
            {"type": "kv", "title": "策略解释", "items": policy_items},
        ]
        if joined is not None and gid not in joined:
            note = "当前群列表中未找到该群；以下策略可能为残留记录，不计入已加入群数。"
            if inv.get("stale"):
                note += "群列表为缓存，暂不据此判定已退群。"
            blocks.append({"type": "note", "text": note, "tone": "warn"})
        elif inferred:
            blocks.append(
                {
                    "type": "note",
                    "text": f"该群尚无 gatekeeper 记录：模式按默认（{self._mode_text(mode)}）"
                    "解释，限制状态未知，不代表已检查正常。",
                    "tone": "muted",
                }
            )
        if snap_err:
            blocks.append({"type": "note", "text": snap_err, "tone": "muted"})
        return {
            "title": f"群详情 · {gid}",
            "subtitle": None,
            "blocks": blocks,
            "footer": f"数据时间 {_hm(time.time())} · 策略允许不等于必定响应",
        }

    # ===================== 工具 =====================
    def _paginate(self, rows: list, page_arg: str):
        total = len(rows)
        pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
        if page_arg == "":
            number = 1
        else:
            if not page_arg.isdigit() or int(page_arg) <= 0:
                return f"页码须为正整数，例如 /status groups 2。共 {total} 条，{pages} 页。"
            number = int(page_arg)
            if number > pages:
                return f"页码超出范围：共 {pages} 页（1–{pages}）。"
        start = (number - 1) * PAGE_SIZE
        return number, pages, rows[start:start + PAGE_SIZE]

    def _error_view(self, title: str, message: str) -> dict:
        return {
            "title": title,
            "subtitle": None,
            "blocks": [{"type": "note", "text": message, "tone": "warn"}],
            "footer": f"数据时间 {_hm(time.time())}",
        }

    def _text_view(self, view: dict) -> str:
        lines: list[str] = []
        if view.get("title"):
            lines.append(view["title"])
        if view.get("subtitle"):
            lines.append(view["subtitle"])
        for block in view.get("blocks") or []:
            if lines:
                lines.append("")
            if block["type"] == "kv":
                for idx, section in enumerate(_kv_sections(block)):
                    if idx:
                        lines.append("")
                    if section.get("title"):
                        lines.append(f"【{section['title']}】")
                    for label, value, _tone in section["items"]:
                        lines.append(f"{label}：{value}")
            elif block["type"] == "table":
                if block.get("title"):
                    lines.append(f"【{block['title']}】")
                if not block["rows"]:
                    lines.append(block.get("empty") or "（无记录）")
                else:
                    for row in block["rows"]:
                        lines.append(" ｜ ".join(str(cell[0]) for cell in row))
            else:
                lines.append(block["text"])
        if view.get("footer"):
            lines.append("")
            lines.append(view["footer"])
        return "\n".join(lines)

    def _cache_key(self, event: AstrMessageEvent, admin: bool, sub: str, params: str) -> str:
        origin = str(event.unified_msg_origin)
        platform_id = origin.split(":")[0]
        if event.get_group_id():
            where = f"g{event.get_group_id()}"
        else:
            where = f"u{event.get_sender_id()}"
        return f"{platform_id}|{'admin' if admin else 'public'}|{where}|{sub}|{params}"

    def _card_get(self, key: str) -> str | None:
        item = self._cards.get(key)
        if not item:
            return None
        stamp, path = item
        if time.monotonic() - stamp > CARD_TTL or not os.path.exists(path):
            self._cards.pop(key, None)
            return None
        self._cards.move_to_end(key)
        return path

    def _card_put(self, key: str, path: str) -> None:
        self._cards[key] = (time.monotonic(), path)
        self._cards.move_to_end(key)
        while len(self._cards) > CARD_CACHE_MAX:
            self._cards.popitem(last=False)

    def _render(self, view: dict) -> str:
        image = _Dashboard(view).build()
        name = f"status_{int(time.time())}_{uuid.uuid4().hex[:8]}.png"
        path = os.path.join(get_astrbot_temp_path(), name)
        image.save(path, format="PNG", optimize=True)
        return path

    def _result(self, event: AstrMessageEvent, view: dict, key: str):
        """视图 → 图片结果；渲染失败时用同一视图输出文字。"""
        path = self._card_get(key)
        if path:
            return event.image_result(path)
        try:
            path = self._render(view)
        except Exception as exc:
            logger.warning("[status] 图片渲染失败，改用文字兜底：%s", _brief(exc, 200))
            return event.plain_result(self._text_view(view))
        self._card_put(key, path)
        return event.image_result(path)

    # ===================== 帮助 / 用法 =====================
    @staticmethod
    def _usage_text() -> str:
        return (
            "未知参数。\n"
            "用法：/status ｜ /status help ｜ /status groups [页码] ｜ "
            "/status group <群ID> ｜ /status bans [页码] ｜ /status plugins [页码] ｜ "
            "/status runtime ｜ /status refresh"
        )

    @staticmethod
    def _help_text(admin: bool, is_group: bool) -> str:
        lines = [
            "状态查询帮助",
            "/status — 查看运行概览" + ("（含本群状态）" if is_group else ""),
            "/status help — 显示本帮助",
        ]
        if admin:
            lines.append("")
            if is_group:
                lines.append("以下查询请私聊使用：")
            lines.extend(
                [
                    "/status groups [页码] — 群列表",
                    "/status group <群ID> — 单群详情",
                    "/status bans [页码] — 禁言与恢复等待",
                    "/status plugins [页码] — 插件列表",
                    "/status runtime — 运行详情与数据来源",
                    "/status refresh — 刷新群列表缓存",
                ]
            )
        lines.append("")
        lines.append("群名称、群 ID 与其他群的限制明细仅机器人管理员私聊可见。")
        lines.append("禁言信息来自 gatekeeper 记录，是已知记录而非实时核验。")
        return "\n".join(lines)

    # ===================== 命令入口 =====================
    @filter.command("status")
    async def status_cmd(self, event: AstrMessageEvent):
        """查看 bot 运行状态（公开概览 / 管理员明细）。"""
        args = event.message_str.split()[1:]
        sub = args[0].lower() if args else ""
        gid_here = str(event.get_group_id() or "")
        is_group = bool(gid_here)
        admin = bool(event.is_admin())

        if sub in ("help", "?", "-h", "帮助"):
            yield event.plain_result(self._help_text(admin, is_group))
            return

        admin_only = {"groups", "group", "bans", "plugins", "runtime", "refresh"}
        if sub in admin_only:
            if not admin:
                yield event.plain_result("仅机器人管理员可在私聊使用该查询。")
                return
            if is_group:
                yield event.plain_result("请私聊使用该查询。")
                return
        elif sub:
            yield event.plain_result(self._usage_text())
            return

        if sub == "group":
            raw = args[1] if len(args) > 1 else ""
            if not raw.isdigit():
                yield event.plain_result("用法：/status group <群ID>（纯数字群号）")
                return
        elif sub in ("groups", "bans", "plugins"):
            if len(args) > 2:
                yield event.plain_result(self._usage_text())
                return

        snap, snap_err = self._snapshot()

        # 只有需要成员范围或主动刷新的子命令才取群列表；plugins / runtime 只读本地
        if sub in ("", "groups", "group", "bans", "refresh"):
            try:
                inv = await self._inventory(event, snap=snap, manual=(sub == "refresh"))
            except _Cooldown as exc:
                yield event.plain_result(f"刷新冷却中，请 {exc.seconds} 秒后再试。")
                return
        else:
            inv = self._cached_inv()

        if sub == "refresh":
            if inv.get("groups") is None:
                yield event.plain_result(
                    f"刷新失败：{inv.get('error') or '未知原因'}\n"
                    "当前没有可用群列表（未知，不是 0 群）。未改任何数据。"
                )
                return
            if inv.get("stale") or inv.get("error"):
                # _stale_inv 会带着旧列表返回，不能只看 groups 是否为 None
                yield event.plain_result(
                    f"刷新失败：{inv.get('error') or '未知原因'}\n"
                    f"保留上次缓存：{len(inv['groups'])} 群 · "
                    f"{_hms(inv.get('observed_at'))} 采集。未改任何数据。"
                )
                return
            source = {"adapter": "QQ 适配器", "gatekeeper": "gatekeeper 快照"}.get(
                str(inv.get("source") or ""), "—"
            )
            yield event.plain_result(
                f"群列表已刷新：{len(inv['groups'])} 群 · {_hms(inv.get('observed_at'))} · {source}\n"
                "未扫描禁言状态，也未修改任何策略。"
            )
            return

        page_arg = args[1] if len(args) > 1 else ""
        if sub == "groups":
            view = self._view_groups(snap, snap_err, inv, page_arg)
        elif sub == "bans":
            view = self._view_bans(snap, snap_err, inv, page_arg)
        elif sub == "plugins":
            view = self._view_plugins(page_arg)
        elif sub == "runtime":
            view = self._view_runtime(event, snap, snap_err, inv)
        elif sub == "group":
            view = await self._view_group(event, snap, snap_err, inv, args[1])
        else:
            view = self._view_overview(event, snap=snap, snap_err=snap_err, inv=inv, admin=admin)

        params = "|".join(args[1:])
        yield self._result(event, view, self._cache_key(event, admin, sub or "overview", params))

    # ===================== 群增减 notice =====================
    @filter.event_message_type(EventMessageType.GROUP_MESSAGE, priority=1)
    async def on_group_notice(self, event: AstrMessageEvent):
        """加退群事件只标记缓存待更新，不立刻请求、不写任何策略。"""
        raw = getattr(getattr(event, "message_obj", None), "raw_message", None)
        if not isinstance(raw, dict) or raw.get("post_type") != "notice":
            return
        if raw.get("notice_type") not in ("group_increase", "group_decrease"):
            return
        self_id = str(raw.get("self_id") or "")
        if str(raw.get("user_id") or "") == self_id:
            self._inv_dirty = True
            self._inv_dirty_at = time.time()
