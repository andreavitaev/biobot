import os
import re
import io
import sys
import json
import math
import time
import heapq
import shutil
import random
import zipfile
import sqlite3
import calendar
import itertools
import functools
import threading
import traceback
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Optional, Tuple, List, Dict

import telebot
from telebot.handler_backends import ContinueHandling
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton, InlineQueryResultArticle, InputTextMessageContent

# CONFIGS
def load_bot_token() -> str:
    """
    Приоритет:
      1) переменные окружения (сервер): BOT_TOKEN / TELEGRAM_BOT_TOKEN
      2) локальный конфиг config_local.py (ПК/тест)
    """
    token = (os.environ.get("BOT_TOKEN") or os.environ.get("TELEGRAM_BOT_TOKEN") or "").strip()
    if token:
        return token
    try:
        import config_local  # type: ignore
        token = str(getattr(config_local, "BOT_TOKEN", "") or "").strip()
        if token:
            return token
    except Exception:
        pass
    raise RuntimeError(
        "⚠️Ошибка: BOT_TOKEN не задан. Укажите переменную окружения BOT_TOKEN "
        "или создайте файл config_local.py с BOT_TOKEN = '...' рядом с файлом запуска бота."
    )
BOT_TOKEN = load_bot_token()

def load_owner_id(default_id: int) -> int:
    raw = (os.environ.get("OWNER_ID") or os.environ.get("CREATOR_ID") or "").strip()
    if raw.isdigit():
        return int(raw)
    try:
        import config_local  # type: ignore
        v = getattr(config_local, "OWNER_ID", None)
        if v is not None and str(v).isdigit():
            return int(v)
        v = getattr(config_local, "CREATOR_ID", None)
        if v is not None and str(v).isdigit():
            return int(v)
    except Exception:
        pass
    return int(default_id)
CREATOR_ID = load_owner_id(7739179390)
OWNER_ID = CREATOR_ID

# ссылки
IRIS_BOT_LINK = "http://t.me/iris_cm_bot"
URL_COMMANDS = "https://teletype.in/@biowar/commands"
URL_SUPPORT_CHAT = "https://t.me/dnd_bot_tgk?direct"
URL_DEV_CHANNEL = "https://t.me/dnd_bot_tgk"
# миниатюры
INLINE_THUMB_LAB_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/lab.png"
INLINE_THUMB_BAL_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/balance.png"
INLINE_THUMB_CALC_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/calculate.png"  
INLINE_THUMB_CORP_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/corp.png"
INLINE_THUMB_INFECT_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/infect.png"
INLINE_THUMB_RP_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/rp.png"
# запасной вариант
INLINE_THUMB_DEFAULT_URL = "https://raw.githubusercontent.com/andreavitaev/boss-rush-assets/main/thumb_1.jpg"

ONLINE_TTL_SECONDS = 300  # 5 минут онлайн по последней активности с ботом

# PATHS / DB
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
DB_PATH = os.path.join(DATA_DIR, "bio_war.db")
DELETED_DB_PATH = os.path.join(DATA_DIR, "deleted_labs.db")
OLD_DATA_DIR = os.path.join(BASE_DIR, "old_data")
OLD_DB_PATH = os.path.join(OLD_DATA_DIR, "bio_war.db")
OLD_DB_WAL_PATH = OLD_DB_PATH + "-wal"
OLD_DB_IMPORT_MARKER_PATH = os.path.join(DATA_DIR, "old_db_import_state.json")
os.makedirs(DATA_DIR, exist_ok=True)

DB_EXPORTS_DIR = os.path.join(DATA_DIR, "db_exports")
DB_BACKUP_DIR = os.path.join(DATA_DIR, "db_backup")
DB_IMPORTS_DIR = os.path.join(DATA_DIR, "db_imports")

DB_BACKUP_MAIN_PATH = os.path.join(DB_BACKUP_DIR, "bio_war_backup.db")
DB_BACKUP_MAIN_WAL_PATH = DB_BACKUP_MAIN_PATH + "-wal"
DB_BACKUP_DELETED_PATH = os.path.join(DB_BACKUP_DIR, "deleted_labs_backup.db")

os.makedirs(DB_EXPORTS_DIR, exist_ok=True)
os.makedirs(DB_BACKUP_DIR, exist_ok=True)
os.makedirs(DB_IMPORTS_DIR, exist_ok=True)

LEGACY_DB_PATH = os.path.join(BASE_DIR, "bio_war.db")
LEGACY_DELETED_DB_PATH = os.path.join(BASE_DIR, "deleted_labs.db")

FORCE_IMPORT_OLD_DB = str(os.environ.get("FORCE_IMPORT_OLD_DB", "") or "").strip() == "1"

os.makedirs(DATA_DIR, exist_ok=True)

# Random infection events
RANDOM_EVENTS_PATH = os.path.join(DATA_DIR, "random_events.txt")
_RANDOM_EVENTS_CACHE: Optional[list[str]] = None

# RP actions
RP_ACTIONS_PATH = os.path.join(DATA_DIR, "rp_actions.txt")
_RP_ACTIONS_CACHE: Optional[dict] = None
_RP_ACTIONS_CACHE_MTIME: float = -1.0

# Miss texts
DUEL_MISALIGN_PATH = os.path.join(DATA_DIR, "misalign.txt")
_DUEL_MISALIGN_CACHE: Optional[list[str]] = None
_DUEL_MISALIGN_CACHE_MTIME: float = -1.0

# emoji pack viewer cache
EMOJI_PACK_PAGE_SIZE = 50
_EMOJI_PACK_VIEW_CACHE: Dict[str, dict] = {}

def load_random_events() -> list[str]:
    global _RANDOM_EVENTS_CACHE
    if _RANDOM_EVENTS_CACHE is not None:
        return _RANDOM_EVENTS_CACHE
    items: list[str] = []
    try:
        with open(RANDOM_EVENTS_PATH, "r", encoding="utf-8") as f:
            for line in f:
                s = (line or "").strip()
                if not s or s.startswith("#"):
                    continue
                items.append(s)
    except Exception:
        pass

    if not items:
        items = [
            "При подготовке к спецоперации ячейка с патогеном разбилась. (придумать разные причины)",
        ]
    _RANDOM_EVENTS_CACHE = items
    return items

def pick_random_event_text() -> str:
    items = load_random_events()
    try:
        return random.choice(items)
    except Exception:
        return "Произошёл непредвиденный сбой во время операции."

def _parse_gendered_text_line(raw_line: str):
    s = re.sub(r"\s+", " ", str(raw_line or "").strip())
    if not s or s.startswith("#"):
        return None

    if "/" in s:
        female_raw, male_raw = s.split("/", 1)
        female = re.sub(r"\s+", " ", female_raw.strip())
        male = re.sub(r"\s+", " ", male_raw.strip())
        return {
            "common": "",
            "female": female,
            "male": male,
        }

    return {
        "common": s,
        "female": "",
        "male": "",
    }

def load_duel_misalign_texts() -> list[str]:
    global _DUEL_MISALIGN_CACHE, _DUEL_MISALIGN_CACHE_MTIME

    try:
        mtime = float(os.path.getmtime(DUEL_MISALIGN_PATH))
    except Exception:
        mtime = -1.0

    if _DUEL_MISALIGN_CACHE is not None and mtime == _DUEL_MISALIGN_CACHE_MTIME:
        return _DUEL_MISALIGN_CACHE

    items: list[str] = []
    try:
        with open(DUEL_MISALIGN_PATH, "r", encoding="utf-8") as f:
            for line in f:
                s = (line or "").strip()
                if not s or s.startswith("#"):
                    continue
                row = _parse_gendered_text_line(line)
                if row:
                    items.append(row)
    except Exception:
        pass

    if not items:
        items = [
            {"common": "внезапным манёвром сбил концентрацию соперника", "female": "", "male": ""}
        ]

    _DUEL_MISALIGN_CACHE = items
    _DUEL_MISALIGN_CACHE_MTIME = mtime
    return items

def pick_duel_misalign_text(actor_id: int = 0) -> str:
    items = load_duel_misalign_texts()
    try:
        row = random.choice(items)
    except Exception:
        row = {"common": "ловко сбил концентрацию соперника", "female": "", "male": ""}

    g = get_user_gender(int(actor_id)) if int(actor_id or 0) > 0 else "male"

    common = str(row.get("common") or "").strip()
    female = str(row.get("female") or "").strip()
    male = str(row.get("male") or "").strip()

    if common:
        return common
    if g == "female" and female:
        return female
    if g == "male" and male:
        return male
    return male or female or "ловко сбил концентрацию соперника"

def load_rp_actions() -> dict:
    global _RP_ACTIONS_CACHE, _RP_ACTIONS_CACHE_MTIME

    try:
        mtime = float(os.path.getmtime(RP_ACTIONS_PATH))
    except Exception:
        mtime = -1.0

    if _RP_ACTIONS_CACHE is not None and mtime == _RP_ACTIONS_CACHE_MTIME:
        return _RP_ACTIONS_CACHE

    out = {}
    try:
        with open(RP_ACTIONS_PATH, "r", encoding="utf-8") as f:
            for raw in f:
                row = _parse_rp_action_file_line(raw)
                if not row:
                    continue
                out[row["trigger_key"]] = row
    except Exception:
        out = {}

    _RP_ACTIONS_CACHE = out
    _RP_ACTIONS_CACHE_MTIME = mtime
    return out

def get_rp_action(trigger: str):
    return load_rp_actions().get((trigger or "").strip().lower())

def _rp_action_text_for_output(action: dict, actor_gender: str = "") -> str:
    g = str(actor_gender or "").strip().lower()

    common = re.sub(r"\s+", " ", str(action.get("action_text_common") or "").strip())
    female = re.sub(r"\s+", " ", str(action.get("action_text_female") or "").strip())
    male = re.sub(r"\s+", " ", str(action.get("action_text_male") or "").strip())
    legacy = re.sub(r"\s+", " ", str(action.get("action_text") or "").strip())

    if common:
        return common

    if g == "female" and female:
        return female

    if g == "male" and male:
        return male

    if male:
        return male
    if female:
        return female
    return legacy

def _normalize_rp_trigger(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip()).lower()

def _split_rp_action_text_variants(raw_text: str) -> dict:
    txt = re.sub(r"\s+", " ", (raw_text or "").strip())
    if not txt:
        return {
            "action_text": "",
            "action_text_common": "",
            "action_text_female": "",
            "action_text_male": "",
        }

    if "/" not in txt:
        return {
            "action_text": txt,
            "action_text_common": txt,
            "action_text_female": "",
            "action_text_male": "",
        }

    female_raw, male_raw = txt.split("/", 1)
    female = re.sub(r"\s+", " ", (female_raw or "").strip())
    male = re.sub(r"\s+", " ", (male_raw or "").strip())

    if female and male:
        default_text = male
    else:
        default_text = female or male

    return {
        "action_text": default_text,
        "action_text_common": "",
        "action_text_female": female,
        "action_text_male": male,
    }

def _parse_rp_action_file_line(raw_line: str):
    s = (raw_line or "").strip()
    if not s or s.startswith("#"):
        return None

    parts = [p.strip() for p in s.split("|")]

    emoji = ""
    premium_id = ""
    trigger = ""
    action_text_raw = ""
    stat1 = ""
    stat2 = ""

    if len(parts) >= 4 and (parts[1].isdigit() or parts[1] == ""):
        while len(parts) < 6:
            parts.append("")
        emoji = parts[0]
        premium_id = parts[1]
        trigger = parts[2]
        action_text_raw = parts[3]
        stat1 = parts[4]
        stat2 = parts[5]
    else:
        while len(parts) < 5:
            parts.append("")
        emoji = parts[0]
        premium_id = ""
        trigger = parts[1]
        action_text_raw = parts[2]
        stat1 = parts[3]
        stat2 = parts[4]

    emoji = re.sub(r"\s+", " ", (emoji or "").strip())
    premium_id = (premium_id or "").strip()
    trigger = re.sub(r"\s+", " ", (trigger or "").strip())
    stat1 = re.sub(r"\s+", " ", (stat1 or "").strip())
    stat2 = re.sub(r"\s+", " ", (stat2 or "").strip())

    if not trigger or not action_text_raw.strip():
        return None

    text_variants = _split_rp_action_text_variants(action_text_raw)
    key = trigger.lower()

    return {
        "emoji": emoji,
        "premium_id": premium_id,
        "trigger": trigger,
        "trigger_key": key,
        "action_text": text_variants["action_text"],
        "action_text_common": text_variants["action_text_common"],
        "action_text_female": text_variants["action_text_female"],
        "action_text_male": text_variants["action_text_male"],
        "stat1": stat1,
        "stat2": stat2,
    }

def load_personal_rp_actions(user_id: int) -> dict:
    rows = db_all(
        "SELECT action_id, user_id, trigger, trigger_key, emoji, premium_id, action_text, uses_count, created_at "
        "FROM personal_rp_actions WHERE user_id=? ORDER BY action_id ASC",
        (int(user_id),)
    ) or []

    out = {}
    for r in rows:
        key = (r["trigger_key"] or "").strip().lower()
        if not key:
            continue
        out[key] = {
            "source": "personal",
            "action_id": int(r["action_id"]),
            "user_id": int(r["user_id"]),
            "emoji": (r["emoji"] or "").strip(),
            "premium_id": (r["premium_id"] or "").strip(),
            "trigger": (r["trigger"] or "").strip(),
            "trigger_key": key,
            "action_text": (r["action_text"] or "").strip(),
            "stat1": "",
            "stat2": "",
            "uses_count": int(r["uses_count"] or 0),
        }
    return out

def _all_rp_actions_for_user(user_id: int) -> list[dict]:
    actions = []
    actions.extend(load_personal_rp_actions(int(user_id)).values())
    for a in load_rp_actions().values():
        row = dict(a)
        row["source"] = "global"
        actions.append(row)

    actions.sort(key=lambda a: len((a.get("trigger") or "").strip()), reverse=True)
    return actions

def _encode_rp_action_ref(action: dict) -> str:
    if str(action.get("source") or "") == "personal":
        return f"p:{int(action['action_id'])}"
    return f"g:{str(action['trigger_key'])}"

def _resolve_rp_action_ref(action_ref: str, actor_id: int):
    ref = str(action_ref or "").strip()
    if ref.startswith("p:"):
        try:
            aid = int(ref.split(":", 1)[1])
        except Exception:
            return None
        row = db_one(
            "SELECT action_id, user_id, trigger, trigger_key, emoji, premium_id, action_text, uses_count "
            "FROM personal_rp_actions WHERE action_id=? AND user_id=? LIMIT 1",
            (aid, int(actor_id))
        )
        if not row:
            return None
        return {
            "source": "personal",
            "action_id": int(row["action_id"]),
            "user_id": int(row["user_id"]),
            "emoji": (row["emoji"] or "").strip(),
            "premium_id": (row["premium_id"] or "").strip(),
            "trigger": (row["trigger"] or "").strip(),
            "trigger_key": (row["trigger_key"] or "").strip(),
            "action_text": (row["action_text"] or "").strip(),
            "stat1": "",
            "stat2": "",
            "uses_count": int(row["uses_count"] or 0),
        }

    if ref.startswith("g:"):
        key = ref.split(":", 1)[1].strip().lower()
        action = get_rp_action(key)
        if action:
            out = dict(action)
            out["source"] = "global"
            return out
        return None

    action = get_rp_action(ref)
    if action:
        out = dict(action)
        out["source"] = "global"
        return out
    return None

def _inc_personal_rp_use(action: dict):
    if str(action.get("source") or "") != "personal":
        return
    db_exec(
        "UPDATE personal_rp_actions SET uses_count=COALESCE(uses_count,0)+1 WHERE action_id=?",
        (int(action["action_id"]),),
        commit=True
    )

def _parse_mrp_create_from_text(text: str):
    raw = strip_bio_prefix((text or "").strip())
    if not raw:
        return None

    first, _, _ = raw.partition("\n")
    first = first.strip()

    if first.startswith("+"):
        first = first[1:].lstrip()

    low = first.lower()
    if not low.startswith("мрп "):
        return None

    body = first[4:].strip()
    parts = [p.strip() for p in body.split("/")]
    if len(parts) != 3:
        return None

    trigger = re.sub(r"\s+", " ", parts[0].strip())
    emoji_part = re.sub(r"\s+", " ", parts[1].strip())
    action_text = re.sub(r"\s+", " ", parts[2].strip())

    if not trigger or not action_text:
        return None

    emoji = ""
    premium_id = ""

    ep = emoji_part.split()
    if ep:
        emoji = ep[0].strip()
    if len(ep) >= 2:
        premium_id = ep[1].strip()

    return {
        "trigger": trigger,
        "trigger_key": _normalize_rp_trigger(trigger),
        "emoji": emoji,
        "premium_id": premium_id,
        "action_text": action_text,
    }

def render_personal_rp_list_text(user_id: int) -> str:
    rows = db_all(
        "SELECT action_id, trigger, emoji, premium_id, uses_count "
        "FROM personal_rp_actions WHERE user_id=? ORDER BY action_id ASC",
        (int(user_id),)
    ) or []

    lines = ["📋 Ваш список личных рп команд:", ""]

    if not rows:
        lines.append("<blockquote expandable>Список пока пуст.</blockquote>")
    else:
        lines.append("<blockquote expandable>")
        for idx, r in enumerate(rows, 1):
            emo = rp_premium_emoji_html((r["emoji"] or "").strip(), (r["premium_id"] or "").strip())
            lines.append(
                f"{idx}.{emo}| <code>{h((r['trigger'] or '').strip())}</code> → {int(r['uses_count'] or 0)}"
            )
        lines.append("</blockquote>")

    lines.append("💬 Чтобы создать личную рп команду, введите\n\"<code>+Мрп</code>\" <b>[название] / [эмодзи] [айди премиум эмодзи (не обязятельно)] / [текст рп действия]</b>")
    lines.append("Чтобы удалить личную рп команду — \"<code>-Мрп</code>\" <b>[название / номер]</b>")

    return "\n".join(lines)

def random_event_pct(qualification_level: int) -> float:
    try:
        q = int(qualification_level or 0)
    except Exception:
        q = 0
    pct = 12.0 - (q // 10) * 0.1 # шанс срабатывания случайного события
    if pct < 5.0:
        pct = 5.0
    return float(pct)

def ids_report_pct(attacker_ids: int, target_ids: int) -> int:
    """5% при равенстве; +5% за каждый IDS цели сверх IDS атакующего; max 100%. Если IDS цели ниже — 0%."""
    try:
        a = int(attacker_ids or 0)
    except Exception:
        a = 0
    try:
        t = int(target_ids or 0)
    except Exception:
        t = 0

    diff = t - a
    pct = 5 + diff * 5
    if diff < 0:
        pct = 0
    if pct > 100:
        pct = 100
    if pct < 0:
        pct = 0
    return int(pct)

def ids_should_fire(attacker_ids: int, target_ids: int) -> bool:
    pct = ids_report_pct(attacker_ids, target_ids)
    if pct <= 0:
        return False
    return random.randint(1, 100) <= pct

def render_ids_report(*, target_id: int, attempts: int, kind: str, organizer_tag: str, result_text: str) -> str:
    """
    kind: 'infect' | 'sabotage'
    """
    ensure_lab_exists(int(target_id))
    lab = get_lab(int(target_id))
    u = get_user_row(int(target_id))
    lab_name = (lab["lab_name"] or "").strip()
    if not lab_name:
        lab_name = default_lab_name(u, int(target_id))

    attempts = int(attempts) if attempts is not None else 1
    if attempts < 1:
        attempts = 1
    w = _ru_form(attempts, "попытка", "попытки", "попыток")
    what = "Вашего заражения" if kind == "infect" else "вторжения в Вашу лабораторию"

    return (
        f"🕵️‍♂️ Служба безопасности лаборатории {h(lab_name)} докладывает:\n"
        f"Была произведена как минимум {attempts} {w} {what}\n"
        f"Организатор: {organizer_tag}\n\n"
        f"{result_text}"
    )

#  IPS Autoanswer 
def _auto_state(uid: int):
    row = db_one(
        "SELECT user_id, enabled, enabled_at, reset_at, used, waiting_no_pathogens, waiting_since, "
        "COALESCE(waiting_hot,0) AS waiting_hot, COALESCE(waiting_hot_since,0) AS waiting_hot_since, "
        "last_warn_ts "
        "FROM autoanswer_state WHERE user_id=?",
        (int(uid),)
    )
    if row:
        return row
    db_exec("INSERT OR IGNORE INTO autoanswer_state(user_id) VALUES (?)", (int(uid),), commit=True)
    return db_one(
        "SELECT user_id, enabled, enabled_at, reset_at, used, waiting_no_pathogens, waiting_since, "
        "COALESCE(waiting_hot,0) AS waiting_hot, COALESCE(waiting_hot_since,0) AS waiting_hot_since, "
        "last_warn_ts "
        "FROM autoanswer_state WHERE user_id=?",
        (int(uid),)
    )

def _auto_limit_from_ips(ips_level: int) -> int:
    try:
        v = int(ips_level or 0)
    except Exception:
        v = 0
    if v < 1:
        v = 1
    return v

def _auto_reset_if_needed(uid: int, now: int):
    st = _auto_state(uid)
    if not st:
        return
    if int(st["enabled"] or 0) != 1:
        return

    enabled_at = int(st["enabled_at"] or 0)
    reset_at = int(st["reset_at"] or 0)

    if enabled_at <= 0:
        enabled_at = now
        reset_at = now + 86400
        db_exec(
            "UPDATE autoanswer_state SET enabled_at=?, reset_at=? WHERE user_id=?",
            (int(enabled_at), int(reset_at), int(uid)),
            commit=True
        )
        return

    if reset_at <= 0:
        reset_at = enabled_at + 86400
        db_exec("UPDATE autoanswer_state SET reset_at=? WHERE user_id=?", (int(reset_at), int(uid)), commit=True)
        return

    if reset_at <= now:
        db_exec(
            "UPDATE autoanswer_state SET used=0, reset_at=?, waiting_no_pathogens=0, waiting_since=0, "
            "waiting_hot=0, waiting_hot_since=0 WHERE user_id=?",
            (int(now + 86400), int(uid)),
            commit=True
        )

def _auto_available(uid: int, ips_level: int, now: int) -> int:
    _auto_reset_if_needed(uid, now)
    st = _auto_state(uid)
    if not st or int(st["enabled"] or 0) != 1:
        return 0
    limit = _auto_limit_from_ips(ips_level)
    used = int(st["used"] or 0)
    return max(0, limit - used)

def kb_autoanswer_status(uid: int) -> InlineKeyboardMarkup:
    st = _auto_state(int(uid))
    enabled = int(st["enabled"] or 0) if st else 0
    kb = InlineKeyboardMarkup()
    if enabled == 1:
        kb.add(InlineKeyboardButton("Выключить", callback_data=f"{CB_AO_TOGGLE}:{uid}:0", style="danger"))
    else:
        kb.add(InlineKeyboardButton("Включить", callback_data=f"{CB_AO_TOGGLE}:{uid}:1", style="success"))
    return kb

def kb_autoanswer_open(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Статус автоответчика", callback_data=f"{CB_AO_MENU}:{uid}", style="primary"))
    return kb

def render_autoanswer_status(uid: int) -> str:
    ensure_lab_exists(int(uid))
    lab = get_lab(int(uid))
    ips_level = int(lab["ips"] or 1)

    now = now_ts()
    _auto_reset_if_needed(int(uid), now)
    st = _auto_state(int(uid))

    enabled = int(st["enabled"] or 0) if st else 0
    used = int(st["used"] or 0) if st else 0
    reset_at = int(st["reset_at"] or 0) if st else 0

    limit = _auto_limit_from_ips(ips_level)
    avail = max(0, limit - used)
    left = max(0, reset_at - now) if reset_at > 0 else 86400

    status_icon = "⭕" if enabled == 1 else "❌"
    return (
        "🦠 [Автоответчик]:\n"
        "Функция ответного заражения\n\n"
        f"Статус: {status_icon}\n"
        f"✅Доступно авто-ответов: {avail}/{limit}\n"
        f"⏱️Сбросится через {_format_hm_from_seconds(left)}\n\n"
        "💬Для увеличения лимита автоответов, используйте команду \"<code>Био +предотвращение</code>\""
    )

def _auto_mark_used_report(uid: int, chat_id: int, msg_id: int) -> bool:
    r = db_one(
        "SELECT 1 FROM autoanswer_used_reports WHERE user_id=? AND chat_id=? AND msg_id=?",
        (int(uid), int(chat_id), int(msg_id))
    )
    if r:
        return True
    db_exec(
        "INSERT OR IGNORE INTO autoanswer_used_reports(user_id,chat_id,msg_id,ts) VALUES (?,?,?,?)",
        (int(uid), int(chat_id), int(msg_id), int(now_ts())),
        commit=True
    )
    return False

def _chat_has_user(chat_id: int, user_id: int) -> bool:
    r = db_one(
        "SELECT 1 FROM chat_members WHERE chat_id=? AND user_id=? LIMIT 1",
        (int(chat_id), int(user_id))
    )
    return r is not None

def _auto_send_reply(chat_id: int, reply_to: int, text: str):
    try:
        bot.send_message(
            int(chat_id),
            text,
            reply_to_message_id=int(reply_to) if reply_to else None,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    except Exception:
        try:
            bot.send_message(int(chat_id), text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            pass

def _auto_header(defender_id: int, chat_id: int, icon: str) -> str:
    if int(chat_id) < 0:
        row = get_user_row(int(defender_id))
        if row:
            nm = display_name(
                row["first_name"] or "",
                row["last_name"] or "",
                row["username"] or "",
                int(defender_id)
            )
        else:
            nm = str(int(defender_id))
        return f"{icon} [Автоответчик <b>{h(nm)}</b>]:\n"
    return f"{icon} [Автоответчик]:\n"

def autoanswer_trigger(defender_id: int, organizer_id: int, chat_id: int, reply_to_msg_id: int, source: str):
    """
    IPS автоответ: defender пытается заразить organizer в ответ.
    source: "IDS" или "CHAT"
    """
    try:
        defender_id = int(defender_id)
        organizer_id = int(organizer_id)
        chat_id = int(chat_id)
        reply_to_msg_id = int(reply_to_msg_id) if reply_to_msg_id else 0
    except Exception:
        return

    if defender_id <= 0 or organizer_id <= 0 or defender_id == organizer_id:
        return

    cd_row = db_one(
        "SELECT COALESCE(until_ts,0) AS u FROM infection_cooldowns WHERE attacker_id=? AND target_id=?",
        (int(defender_id), int(organizer_id))
    )
    cd_until = int(cd_row["u"] if cd_row else 0)
    if cd_until > now_ts():
        return

    now = now_ts()
    ensure_lab_exists(defender_id)

    if source == "IDS" and reply_to_msg_id:
        if _auto_mark_used_report(defender_id, chat_id, reply_to_msg_id):
            return

    st = _auto_state(defender_id)
    if not st or int(st["enabled"] or 0) != 1:
        return

    lab_def = get_lab(defender_id)
    ips_level = int(lab_def["ips"] or 1)

    if int(st["waiting_no_pathogens"] or 0) == 1:
        if int(lab_def["ready_pathogens"] or 0) <= 0:
            return
        db_exec("UPDATE autoanswer_state SET waiting_no_pathogens=0, waiting_since=0 WHERE user_id=?",
                (defender_id,), commit=True)
        st = _auto_state(defender_id)

    if int(st["waiting_hot"] or 0) == 1:
        fr = db_one("SELECT COALESCE(fever_until_ts,0) AS f FROM labs WHERE user_id=?", (defender_id,))
        fu = int(fr["f"] if fr else 0)
        if fu > now:
            return
        db_exec("UPDATE autoanswer_state SET waiting_hot=0, waiting_hot_since=0 WHERE user_id=?",
                (defender_id,), commit=True)
        st = _auto_state(defender_id)

    avail = _auto_available(defender_id, ips_level, now)
    if avail <= 0:
        return

    db_exec("UPDATE autoanswer_state SET used=COALESCE(used,0)+1 WHERE user_id=?",
            (defender_id,), commit=True)

    u_org = get_user_row(organizer_id)
    org_un = (u_org["username"] or "") if u_org else ""
    org_disp = display_name(
        (u_org["first_name"] or "") if u_org else "",
        (u_org["last_name"] or "") if u_org else "",
        org_un,
        organizer_id
    )
    org_tag = tg_mention(int(organizer_id), org_disp, username=org_un)
    org_q = f"«{org_tag}»"

    fr = db_one(
        "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(fever_pathogen,'') AS fp FROM labs WHERE user_id=?",
        (defender_id,)
    )
    fever_until = int(fr["f"] if fr else 0)
    fever_pat = (fr["fp"] if fr else "") or ""
    if fever_until > now:
        auto_vac = int(lab_def["ready_vaccines"] or 0)
    
        if auto_vac > 0:
            status_vac, used_vac = try_use_vaccine(defender_id, min(10, auto_vac))
    
            if status_vac == "OK":
                lab_def = get_lab(defender_id)
    
                txt = (
                    _auto_header(defender_id, chat_id, "💉")
                    +f"Использовано {int(used_vac)} вакцин.\n"
                    + f"Повторяю попытку заражения {org_q}..."
                )
                _auto_send_reply(chat_id, reply_to_msg_id, txt)
    
                fr = db_one(
                    "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(fever_pathogen,'') AS fp FROM labs WHERE user_id=?",
                    (defender_id,)
                )
                fever_until = int(fr["f"] if fr else 0)
                fever_pat = (fr["fp"] if fr else "") or ""
    
            elif status_vac in ("FAIL", "NO_VACCINE"):
                left = max(0, fever_until - now)
                txt = (
                    _auto_header(defender_id, chat_id, "🌡️")
                    + f"❎ Не удалось заразить {org_q}: Горячка, вызванная {_pat_for_fever(fever_pat)}, "
                    + f"время выздоровления {_format_hms(left)}"
                )
                _auto_send_reply(chat_id, reply_to_msg_id, txt)
                db_exec(
                    "UPDATE autoanswer_state SET waiting_hot=1, waiting_hot_since=? WHERE user_id=?",
                    (int(now), defender_id),
                    commit=True
                )
                return
    
        if fever_until > now:
            left = fever_until - now
            txt = (
                _auto_header(defender_id, chat_id, "🌡️")
                + f"❎ Не удалось заразить {org_q}: Горячка, вызванная {_pat_for_fever(fever_pat)}, "
                + f"время выздоровления {_format_hms(left)}"
            )
            _auto_send_reply(chat_id, reply_to_msg_id, txt)
            db_exec(
                "UPDATE autoanswer_state SET waiting_hot=1, waiting_hot_since=? WHERE user_id=?",
                (int(now), defender_id),
                commit=True
            )
            return

    ready = int(lab_def["ready_pathogens"] or 0)
    if ready <= 0:
        txt = (
            _auto_header(defender_id, chat_id, "🧪")
            + f"❎ Не удалось заразить {org_q}: не осталось патогенов"
        )
        _auto_send_reply(chat_id, reply_to_msg_id, txt)
        db_exec("UPDATE autoanswer_state SET waiting_no_pathogens=1, waiting_since=? WHERE user_id=?",
                (int(now), defender_id), commit=True)
        return

    db_exec(
        "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0)>0 THEN ready_pathogens-1 ELSE 0 END "
        "WHERE user_id=?",
        (defender_id,),
        commit=True
    )

    qual = int(lab_def["qualification"] or 1)
    if random.random() * 100.0 < random_event_pct(qual):
        ev = pick_random_event_text()
        txt = (
            _auto_header(defender_id, chat_id, "💢")
            + f"❎ Не удалось заразить {org_q}: {h(ev)}"
        )
        _auto_send_reply(chat_id, reply_to_msg_id, txt)
        return

    def_inf = int(lab_def["infectivity"] or 1)
    trow = db_one(
        "SELECT COALESCE(immunity,0) AS imm, COALESCE(bio_exp,0) AS be FROM labs WHERE user_id=?",
        (organizer_id,)
    )
    org_imm = int(trow["imm"] if trow else 0)
    p_success = infect_success_chance(def_inf, org_imm)
    fail_stack = _get_infection_fail_stack(defender_id, organizer_id, now)
    roll = random.random() * 100.0
    if roll >= p_success:
        _add_infection_fail_stack(defender_id, organizer_id, now)
        txt = (
            _auto_header(defender_id, chat_id, "🛡")
            + f"❎ Не удалось заразить {org_q}: иммунитет справился с заражением"
        )
        _auto_send_reply(chat_id, reply_to_msg_id, txt)
        return

    texp = int(trow["be"] if trow else 0)
    gained = _calc_infection_gain_with_fail_stack(texp, fail_stack)

    let_lvl = int(lab_def["lethality"] or 1)
    inf_days = _calc_inf_days(let_lvl)
    inf_duration_sec = int(inf_days) * 86400
    fever_add = _calc_fever_sec(let_lvl)

    end_ts = now + inf_duration_sec
    next_payout = now + 86400
    if next_payout >= end_ts:
        next_payout = 0

    pathogen_name = (lab_def["pathogen_name"] or "").strip()

    active = db_one(
        "SELECT end_ts FROM infections WHERE attacker_id=? AND target_id=?",
        (defender_id, organizer_id)
    )
    already_active = bool(active and int(active["end_ts"] or 0) > now)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            c.execute(
                "UPDATE labs SET bio_exp=COALESCE(bio_exp,0)+?, bio_res=COALESCE(bio_res,0)+?, "
                "all_bio_res=COALESCE(all_bio_res,0)+?, successful_ops=COALESCE(successful_ops,0)+1, "
                "ops_total=COALESCE(ops_total,0)+1 WHERE user_id=?",
                (gained, gained, gained, defender_id)
            )

            c.execute(
                "UPDATE labs SET bio_exp=CASE "
                "WHEN COALESCE(bio_exp,0) <= 1 THEN COALESCE(bio_exp,0) "
                "WHEN (COALESCE(bio_exp,0) - ?) < 1 THEN 1 "
                "ELSE (COALESCE(bio_exp,0) - ?) END "
                "WHERE user_id=?",
                (gained, gained, organizer_id)
            )

            c.execute(
                "UPDATE labs SET fever_until_ts = CASE WHEN COALESCE(fever_until_ts,0) > ? THEN fever_until_ts + ? ELSE ? END, "
                "fever_pathogen = ? WHERE user_id=?",
                (now, fever_add, now + fever_add, pathogen_name, organizer_id)
            )

            if not already_active:
                c.execute("UPDATE labs SET infected_total=COALESCE(infected_total,0)+1 WHERE user_id=?", (defender_id,))
                c.execute("UPDATE labs SET diseases_total=COALESCE(diseases_total,0)+1 WHERE user_id=?", (organizer_id,))

            c.execute(
                "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name,known_to_target) "
                "VALUES (?,?,?,?,?,?,1,?,1) "
                "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                "start_ts=excluded.start_ts, end_ts=excluded.end_ts, "
                "add_bio_res=excluded.add_bio_res, "
                "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name, known_to_target=1",
                (defender_id, organizer_id, now, end_ts, gained, next_payout, pathogen_name)
            )

            c.execute(
                "INSERT INTO infection_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
                "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
                (defender_id, organizer_id, now + REINFECT_CD_SEC)
            )

            c.execute(
                "DELETE FROM infection_fail_stacks WHERE attacker_id=? AND target_id=?",
                (defender_id, organizer_id)
            )

            c.execute(
                "INSERT OR IGNORE INTO infection_seen(attacker_id,target_id) VALUES (?,?)",
                (defender_id, organizer_id)
            )

            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
    txt = (
        _auto_header(defender_id, chat_id, "🦠")
        + f"✅ Успешное заражение {org_q}\n"
        + f"☣️‍ +{_fmt_k(int(gained))} {exp_word}"
    )
    _auto_send_reply(chat_id, reply_to_msg_id, txt)

DB_LOCK = threading.RLock()

# BOT threaded
bot = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML", threaded=True, num_threads=8)

_ORIG_BOT_CALLBACK_QUERY_HANDLER = bot.callback_query_handler

def _callback_chat_name_ctx_chat_id(cq) -> int:
    try:
        msg = getattr(cq, "message", None)
        chat = getattr(msg, "chat", None)
        return int(getattr(chat, "id", 0) or 0)
    except Exception:
        return 0

def _wrap_callback_with_chat_name_context(fn):
    @functools.wraps(fn)
    def _wrapped(cq, *args, **kwargs):
        set_chat_name_context(_callback_chat_name_ctx_chat_id(cq))
        try:
            return fn(cq, *args, **kwargs)
        finally:
            clear_chat_name_context()
    return _wrapped

def _callback_query_handler_with_chat_name_context(*handler_args, **handler_kwargs):
    decorator = _ORIG_BOT_CALLBACK_QUERY_HANDLER(*handler_args, **handler_kwargs)

    def _decorator(fn):
        return decorator(_wrap_callback_with_chat_name_context(fn))

    return _decorator

bot.callback_query_handler = _callback_query_handler_with_chat_name_context

@dataclass
class _EditJob:
    due: float
    target: tuple
    req_id: int
    text: str
    reply_markup: object
    parse_mode: Optional[str]
    inline_id: Optional[str]
    chat_id: Optional[int]
    msg_id: Optional[int]
    disable_web_page_preview: Optional[bool]

class EditLimiter:
    def __init__(self, bot_obj, global_gap_sec: float = 0.12, per_target_gap_sec: float = 1.05):
        self.bot = bot_obj
        self.global_gap = float(global_gap_sec)
        self.per_target_gap = float(per_target_gap_sec)

        self._lock = threading.RLock()
        self._cv = threading.Condition(self._lock)
        self._pq = [] 
        self._counter = itertools.count()
        self._latest_req: Dict[tuple, int] = {}

        self._last_global = 0.0
        self._last_target: Dict[tuple, float] = {}

        t = threading.Thread(target=self._run, daemon=True)
        t.start()

    def _parse_retry_after(self, e: Exception) -> int:
        s = str(e)
        m = re.search(r"retry after (\d+)", s, flags=re.IGNORECASE)
        return int(m.group(1)) if m else 0

    def _compute_due(self, target: tuple) -> float:
        now = time.time()
        due = now
        due = max(due, self._last_global + self.global_gap)
        due = max(due, self._last_target.get(target, 0.0) + self.per_target_gap)
        return due

    def edit_text(self, *, text: str, reply_markup=None, parse_mode: str = None,
                  inline_id: str = None, chat_id: int = None, msg_id: int = None,
                  disable_web_page_preview: bool = None):
        if inline_id:
            target = ("inline", inline_id)
        else:
            target = ("chat", int(chat_id or 0), int(msg_id or 0))

        with self._lock:
            due = self._compute_due(target)
            req_id = next(self._counter)
            self._latest_req[target] = req_id
            job = _EditJob(due, target, req_id, text, reply_markup, parse_mode, inline_id, chat_id, msg_id, disable_web_page_preview)
            heapq.heappush(self._pq, (job.due, next(self._counter), job))
            self._cv.notify()
        return True

    def _run(self):
        while True:
            with self._lock:
                if not self._pq:
                    self._cv.wait(timeout=0.5)
                    continue
                due, _, job = self._pq[0]
                now = time.time()
                if due > now:
                    self._cv.wait(timeout=min(0.5, due - now))
                    continue
                heapq.heappop(self._pq)

                if self._latest_req.get(job.target) != job.req_id:
                    continue

            try:
                if job.inline_id:
                    self.bot.edit_message_text(
                        job.text,
                        inline_message_id=job.inline_id,
                        reply_markup=job.reply_markup,
                        parse_mode=job.parse_mode,
                        disable_web_page_preview=job.disable_web_page_preview
                    )
                else:
                    self.bot.edit_message_text(
                        job.text,
                        chat_id=job.chat_id,
                        message_id=job.msg_id,
                        reply_markup=job.reply_markup,
                        parse_mode=job.parse_mode,
                        disable_web_page_preview=job.disable_web_page_preview
                    )

                with self._lock:
                    t = time.time()
                    self._last_global = t
                    self._last_target[job.target] = t

            except Exception as e:
                if "message is not modified" in str(e).lower():
                    continue
                ra = self._parse_retry_after(e)
                if ra > 0:
                    with self._lock:
                        self._latest_req[job.target] = job.req_id
                        job.due = time.time() + ra + 0.15
                        heapq.heappush(self._pq, (job.due, next(self._counter), job))
                        self._cv.notify()
                continue

EDIT_LIMITER = EditLimiter(bot, global_gap_sec=0.12, per_target_gap_sec=1.05)

def limited_edit_message_text(*, text: str, reply_markup=None, parse_mode: str = None,
                              inline_id: str = None, chat_id: int = None, msg_id: int = None,
                              disable_web_page_preview: bool = None):
    try:
        EDIT_LIMITER.edit_text(
            text=text,
            reply_markup=reply_markup,
            parse_mode=parse_mode,
            inline_id=inline_id,
            chat_id=chat_id,
            msg_id=msg_id,
            disable_web_page_preview=disable_web_page_preview
        )
    except Exception:
        try:
            if inline_id:
                bot.edit_message_text(text, inline_message_id=inline_id, reply_markup=reply_markup, parse_mode=parse_mode, disable_web_page_preview=disable_web_page_preview)
            else:
                bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id, reply_markup=reply_markup, parse_mode=parse_mode, disable_web_page_preview=disable_web_page_preview)
        except Exception:
            pass

# Имя/username/id бота
try:
    _me = bot.get_me()
    BOT_ID = int(getattr(_me, "id", 0) or 0)
    BOT_USERNAME = _me.username or ""
    BOT_TITLE = (_me.first_name or "").strip() or "Bio War bot"
except Exception:
    BOT_ID = 0
    BOT_USERNAME = ""
    BOT_TITLE = "Bio War bot"

def refresh_bot_identity():
    global BOT_ID, BOT_USERNAME, BOT_TITLE
    try:
        me = bot.get_me()
        BOT_ID = int(getattr(me, "id", 0) or 0)
        BOT_USERNAME = (getattr(me, "username", "") or "").strip()
        BOT_TITLE = (getattr(me, "first_name", "") or "").strip() or "Bio War bot"
        return True
    except Exception:
        return False

# Коды ошибок файлы.txt (анти-спам файлами)
_ERROR_REPORT_LAST: Dict[str, int] = {}
ERROR_REPORT_COOLDOWN_SEC = 60

def _service_notify_user_ids() -> List[int]:
    ids: List[int] = []
    seen = set()

    def _add(v):
        try:
            uid = int(v or 0)
        except Exception:
            return
        if uid <= 0 or uid in seen:
            return
        seen.add(uid)
        ids.append(uid)

    try:
        ensure_creator_role_state()
    except Exception:
        pass

    try:
        _add(get_current_creator_id())
    except Exception:
        pass

    try:
        for r in (get_bot_owners() or []):
            try:
                _add(int(r["user_id"]))
            except Exception:
                pass
    except Exception:
        pass

    if not ids:
        _add(CREATOR_ID)
        _add(OWNER_ID)

    return ids

def _report_notify_user_ids() -> List[int]:
    ids: List[int] = []
    seen = set()

    def _add(v):
        try:
            uid = int(v or 0)
        except Exception:
            return
        if uid <= 0 or uid in seen:
            return
        seen.add(uid)
        ids.append(uid)

    try:
        ensure_creator_role_state()
    except Exception:
        pass

    try:
        _add(get_current_creator_id())
    except Exception:
        pass

    try:
        for r in (get_bot_owners() or []):
            try:
                _add(int(r["user_id"]))
            except Exception:
                pass
    except Exception:
        pass

    try:
        for r in (get_support_agents() or []):
            try:
                _add(int(r["user_id"]))
            except Exception:
                pass
    except Exception:
        pass

    if not ids:
        for uid in _service_notify_user_ids():
            _add(uid)

    return ids

def _send_message_to_report_recipients(text: str, *, parse_mode: str = "HTML", disable_web_page_preview: bool = True) -> bool:
    ok = False
    for uid in _report_notify_user_ids():
        try:
            bot.send_message(
                int(uid),
                text,
                parse_mode=parse_mode,
                disable_web_page_preview=disable_web_page_preview
            )
            ok = True
        except Exception:
            pass
    return ok

def _send_media_to_report_recipients(media_type: str, media_file_id: str, *, caption: str = "", parse_mode: Optional[str] = "HTML") -> bool:
    ok = False
    mtype = str(media_type or "").strip().lower()
    fid = str(media_file_id or "").strip()
    if not fid or mtype not in ("photo", "video"):
        return False

    for uid in _report_notify_user_ids():
        try:
            if mtype == "photo":
                if caption:
                    bot.send_photo(int(uid), fid, caption=caption, parse_mode=parse_mode)
                else:
                    bot.send_photo(int(uid), fid)
            else:
                if caption:
                    bot.send_video(int(uid), fid, caption=caption, parse_mode=parse_mode)
                else:
                    bot.send_video(int(uid), fid)
            ok = True
        except Exception:
            pass

    return ok

def _send_document_to_service_recipients(payload: bytes, filename: str, caption: str = "") -> bool:
    ok = False
    raw = payload if isinstance(payload, (bytes, bytearray)) else bytes(str(payload or ""), "utf-8", errors="replace")

    for uid in _service_notify_user_ids():
        try:
            bio = io.BytesIO(raw)
            bio.name = str(filename or "service_report.txt")
            bot.send_document(int(uid), bio, caption=caption or None)
            ok = True
        except Exception:
            pass

    return ok

def _send_message_to_service_recipients(text: str, *, parse_mode: str = "HTML", disable_web_page_preview: bool = True) -> bool:
    ok = False
    for uid in _service_notify_user_ids():
        try:
            bot.send_message(
                int(uid),
                text,
                parse_mode=parse_mode,
                disable_web_page_preview=disable_web_page_preview
            )
            ok = True
        except Exception:
            pass
    return ok

def send_error_report(context: str, exc: Exception | None = None) -> None:
    try:
        now = int(time.time())
        prev = int(_ERROR_REPORT_LAST.get(context, 0) or 0)
        if (now - prev) < ERROR_REPORT_COOLDOWN_SEC:
            return
        _ERROR_REPORT_LAST[context] = now

        if exc is None:
            tb = traceback.format_exc()
            if not tb or tb.strip() == "NoneType: None":
                tb = "".join(traceback.format_stack(limit=40))
        else:
            tb = "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))

        ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now))
        payload = f"[{ts}] {context}\n\n{tb}".encode("utf-8", errors="replace")

        _send_document_to_service_recipients(
            payload,
            f"bot_error_{now}.txt",
            caption=f"Ошибка бота: {context}"
        )
    except Exception:
        pass

def _thread_excepthook(args):
    try:
        now = int(time.time())
        text = "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback))
        _send_document_to_service_recipients(
            text.encode("utf-8", errors="replace"),
            f"thread_error_{now}.txt",
            caption=f"Поток: {getattr(args.thread, 'name', 'thread')}"
        )
    except Exception:
        pass
    
threading.excepthook = _thread_excepthook

def _sys_excepthook(exc_type, exc_value, exc_tb):
    try:
        now = int(time.time())
        text = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        _send_document_to_service_recipients(
            text.encode("utf-8", errors="replace"),
            f"fatal_error_{now}.txt",
            caption="Необработанная ошибка"
        )
    except Exception:
        pass
    sys.__excepthook__(exc_type, exc_value, exc_tb)

sys.excepthook = _sys_excepthook

# UTILS
def h(text: str) -> str:
    """HTML-escape minimal."""
    if text is None:
        return ""
    return (
        str(text)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )

PREMIUM_EMOJI_ENABLED = True # custom emoji

PREMIUM_EMOJI_IDS: Dict[str, str] = {
    "🔬": "5379679518740978720",
    "💰": "5215420556089776398",
    "☣️": "5332773077094797849",
    "🧬": "5283187323180190072",
    "💊": "5332753204281121154",
    "🥽": "5451679753490670501",
    "💢": "5452001081468922151",
    "🩻": "5451915461295876382",
    "🌡️": "5470049770997292425",    
    "💥": "5197414236413786044",
    "🎯": "5447213996820168272",
    "🦠": "5451936901772616837",
    "☠️": "5370842086658546991",
    "🧿": "5348470396582665977",
    "🛡️": "5348259539458236641",
    "⚗️": "5262680005393025261",
    "💉": "5472317878801800869",
    "🧪": "5411512278740640309",
    "🧫": "5280706833537865059",
    "📟": "5195361551283942795",
    "🛰️": "5444979432710242887",
    "🤖": "5355051922862653659",
    "🧮": "5190741648237161191",
    "⏱️": "5258258882022612173",
    "⛑️": "5264892613630111886",
    "🏷️": "5255806717689631058",
    "✉️": "5447607759421863856",
    "📑": "",
    "📋": "5197269100878907942",
    "🧾": "5444860552310457690",
    "📝": "5334882760735598374",
    "📊": "5431577498364158238",
    "📈": "5332482733010622094",
    "📉": "5449892166627238763",
    "✅": "5447298551841322535",
    "❎": "5445283164207479914",
    "⭕": "5260416304224936047",
    "❌": "5260342697075416641",
    "❗": "5220197908342648622",
    "⚠️": "5447381715293074599",
    "🔒": "5258458340303866282",
    "🔓": "5256212970056224341",
    "🔊": "5260325873688518261",
    "🔇": "5258267368877989660",
    "⏳": "5199457120428249992",
    "⏰": "5258258882022612173",
    "🔁": "5258419835922030550",
    "🤧": "5370880659759831851",
    "🤒": "5373262021556967911",
    "🕵️‍♂️": "",
    "👨‍🔬": "5460722519369591542",
    "👮": "",
    "🥷": "5195316351048121745",
    "👨‍⚕️": "5408834671574294163",
    "🧑‍✈️": "",
    "🧑‍💼": "",
    "🏥": "5264827875588077689",
    "🏣": "5264716824913671598",
    "🏢": "5264733042710181045",
    "💎": "5343636681473935403",
    "🪬": "5276489300207217985",
    "🎁": "5199749070830197566",
    "🔹": "5258255531948146531",
    "💬": "5255727011686553638",
    "👋": "5348172574960427760",
    "⚙️": "5445347129155419150",
}
_RAW_INLINE_KEYBOARD_BUTTON = InlineKeyboardButton
PREMIUM_BUTTON_EMPTY_TEXT = "\u3164"  # невидимый, но не пустой текст для Telegram-кнопок

def _strip_emoji_variation_selectors(s: str) -> str:
    return str(s or "").replace("\ufe0f", "").replace("\ufe0e", "")

def _premium_emoji_id(ch: str) -> str:
    raw = str(ch or "")
    if not raw:
        return ""

    direct = str(PREMIUM_EMOJI_IDS.get(raw, "") or "").strip()
    if direct:
        return direct

    norm = _strip_emoji_variation_selectors(raw)
    if norm != raw:
        direct = str(PREMIUM_EMOJI_IDS.get(norm, "") or "").strip()
        if direct:
            return direct

    for k, v in PREMIUM_EMOJI_IDS.items():
        if _strip_emoji_variation_selectors(str(k)) == norm:
            vv = str(v or "").strip()
            if vv:
                return vv

    return ""

def _premium_emoji_keys() -> list[str]:
    keys = []
    seen = set()

    for k, v in PREMIUM_EMOJI_IDS.items():
        kk = str(k or "")
        vv = str(v or "").strip()
        if not kk or not vv:
            continue

        for candidate in (kk, _strip_emoji_variation_selectors(kk)):
            if candidate and candidate not in seen:
                seen.add(candidate)
                keys.append(candidate)

    keys.sort(key=len, reverse=True)
    return keys

_PREMIUM_EMOJI_KEYS = _premium_emoji_keys()

def _find_premium_emoji_at(text: str, pos: int = 0) -> tuple[str, str]:
    s = str(text or "")
    if pos < 0 or pos >= len(s):
        return "", ""

    for emo in _PREMIUM_EMOJI_KEYS:
        if s.startswith(emo, pos):
            return emo, _premium_emoji_id(emo)
    return "", ""

def premiumize_html_text(text: str) -> str:
    if not PREMIUM_EMOJI_ENABLED or not text:
        return text

    s = str(text)
    out = []
    i = 0
    n = len(s)

    while i < n:
        emo, eid = _find_premium_emoji_at(s, i)
        if emo and eid:
            out.append(f'<tg-emoji emoji-id="{h(eid)}">{h(emo)}</tg-emoji>')
            i += len(emo)
            continue

        out.append(s[i])
        i += 1

    return "".join(out)

def premium_emoji_html(emoji: str) -> str:
    emo = str(emoji or "")
    eid = _premium_emoji_id(emo) if PREMIUM_EMOJI_ENABLED else ""
    if eid:
        return f'<tg-emoji emoji-id="{h(eid)}">{h(emo)}</tg-emoji>'
    return emo

def _rp_pick_single_fallback_emoji(emoji_text: str) -> str:
    raw = re.sub(r"\s+", " ", str(emoji_text or "").strip())
    if not raw:
        return ""

    parts = [p for p in raw.split(" ") if p]
    if not parts:
        return raw

    return parts[0]

def _rp_plain_emoji_html(emoji_text: str) -> str:
    emo = re.sub(r"\s+", " ", str(emoji_text or "").strip())
    if not emo:
        return ""

    out = []
    for ch in emo:
        if ch.isspace():
            out.append(ch)
        else:
            out.append(f"&#{ord(ch)};")
    return "".join(out)

def InlineKeyboardButton(text, *args, **kwargs):
    return _RAW_INLINE_KEYBOARD_BUTTON(text, *args, **kwargs)

def _raw_button_build(
    text: str,
    *,
    callback_data: str = None,
    url: str = None,
    style: str = None,
    icon_custom_emoji_id: str = None
):
    kwargs = {}
    if callback_data is not None:
        kwargs["callback_data"] = callback_data
    if url is not None:
        kwargs["url"] = url
    if style:
        kwargs["style"] = style
    if icon_custom_emoji_id:
        kwargs["icon_custom_emoji_id"] = icon_custom_emoji_id

    try:
        return _RAW_INLINE_KEYBOARD_BUTTON(text, **kwargs)
    except TypeError:
        kwargs.pop("icon_custom_emoji_id", None)
        try:
            return _RAW_INLINE_KEYBOARD_BUTTON(text, **kwargs)
        except TypeError:
            kwargs.pop("style", None)
            return _RAW_INLINE_KEYBOARD_BUTTON(text, **kwargs)

def _ikb_premium_icon_only(
    emoji: str,
    *,
    callback_data: str = None,
    url: str = None,
    style: str = None
):
    emo = str(emoji or "")
    eid = _premium_emoji_id(emo) if PREMIUM_EMOJI_ENABLED else ""

    if eid:
        btn = _raw_button_build(
            PREMIUM_BUTTON_EMPTY_TEXT,
            callback_data=callback_data,
            url=url,
            style=style,
            icon_custom_emoji_id=eid
        )
        if btn:
            return btn

    return _raw_button_build(
        emo,
        callback_data=callback_data,
        url=url,
        style=style
    )

def _ikb_premium_counter(
    emoji: str,
    counter_text: str,
    *,
    callback_data: str = None,
    url: str = None,
    style: str = None
):
    emo = str(emoji or "")
    label = str(counter_text or "").strip()
    eid = _premium_emoji_id(emo) if PREMIUM_EMOJI_ENABLED else ""

    if eid:
        btn = _raw_button_build(
            label if label else PREMIUM_BUTTON_EMPTY_TEXT,
            callback_data=callback_data,
            url=url,
            style=style,
            icon_custom_emoji_id=eid
        )
        if btn:
            return btn

    fallback_text = f"{emo} {label}".strip()
    return _raw_button_build(
        fallback_text,
        callback_data=callback_data,
        url=url,
        style=style
    )

def _ikb_premium_lead(
    emoji: str,
    label_text: str,
    *,
    callback_data: str = None,
    url: str = None,
    style: str = None
):
    emo = str(emoji or "")
    label = str(label_text or "").strip()
    eid = _premium_emoji_id(emo) if PREMIUM_EMOJI_ENABLED else ""

    if eid:
        btn = _raw_button_build(
            label if label else PREMIUM_BUTTON_EMPTY_TEXT,
            callback_data=callback_data,
            url=url,
            style=style,
            icon_custom_emoji_id=eid
        )
        if btn:
            return btn

    fallback_text = f"{emo} {label}".strip()
    return _raw_button_build(
        fallback_text,
        callback_data=callback_data,
        url=url,
        style=style
    )

def now_ts() -> int:
    return int(time.time())

_INVISIBLE_RE = re.compile(r"[\u200b\u200c\u200d\u2060\ufeff]")

_BLANK_LIKE_CHARS = { # Частые "пустые" символы, которыми делают визуально пустое имя
    "\u3164",  # HANGUL FILLER
    "\u2800",  # BRAILLE PATTERN BLANK
    "\u115F",  # HANGUL CHOSEONG FILLER
    "\u1160",  # HANGUL JUNGSEONG FILLER
    "\u17B4",  # KHMER VOWEL INHERENT AQ
    "\u17B5",  # KHMER VOWEL INHERENT AA
}

def _strip_invisible(s: str) -> str:
    s = (s or "")
    s = _INVISIBLE_RE.sub("", s)
    s = s.replace("\u00ad", "")  # soft hyphen
    return s.strip()

def _is_emoji_char(ch: str) -> bool:
    """Приблизительная проверка emoji (достаточно для правила '1 символ')."""
    if not ch:
        return False
    cp = ord(ch)
    return (
        0x1F300 <= cp <= 0x1FAFF  # основной emoji диапазон
        or 0x2600 <= cp <= 0x27BF # misc symbols
        or 0xFE00 <= cp <= 0xFE0F # variation selectors
    )

def _is_bad_single_char_name(s: str) -> bool:
    """
    True если s после очистки = ровно 1 символ и он:
    - "blank-like" (filler/blank), ИЛИ
    - не буква/число/знак препинания/мат.символ/emoji
    """
    s = _strip_invisible(s)
    if len(s) != 1:
        return False

    ch = s

    if ch in _BLANK_LIKE_CHARS:
        return True

    try:
        nm = unicodedata.name(ch, "")
        if "FILLER" in nm or "BLANK" in nm:
            return True
    except Exception:
        pass

    if _is_emoji_char(ch):
        return False

    cat = unicodedata.category(ch)  # 'Lu', 'Nd', 'Po', 'Sm', ...
    if cat.startswith("L"):  # Letter
        return False
    if cat.startswith("N"):  # Number
        return False
    if cat.startswith("P"):  # Punctuation
        return False
    if cat == "Sm":          # Math Symbol
        return False

    return True

_VARIATION_SELECTORS = {"\ufe0e", "\ufe0f"}

def _is_decorative_only_name(s: str) -> bool:
    """
    True если строка после очистки состоит только из символов-декораций (emoji/символы),
    без букв/цифр/пунктуации/мат.символов.
    Это лечит кейс, когда имя = '✔️' и в итоге выглядит пустым.
    """
    t = _strip_invisible(s)
    t = "".join(ch for ch in t if (ch not in _VARIATION_SELECTORS) and (not ch.isspace()))
    if not t:
        return True

    for ch in t:
        cat = unicodedata.category(ch)  # Lu, Nd, Po, Sm, So...
        if cat.startswith("L"):  # letters
            return False
        if cat.startswith("N"):  # numbers
            return False
        if cat.startswith("P"):  # punctuation
            return False
        if cat == "Sm":          # math symbol
            return False

    return True

# имена в боте
_CHAT_USER_NAME_MAX_LEN = 20
_CHAT_NAME_CTX = threading.local()

def _chat_name_ctx_chat_id() -> int:
    try:
        return int(getattr(_CHAT_NAME_CTX, "chat_id", 0) or 0)
    except Exception:
        return 0

def _chat_name_ctx_force_standard() -> bool:
    return bool(getattr(_CHAT_NAME_CTX, "force_standard", False))

def set_chat_name_context(chat_id: int = 0, *, force_standard: bool = False):
    _CHAT_NAME_CTX.chat_id = int(chat_id or 0)
    _CHAT_NAME_CTX.force_standard = bool(force_standard)

def clear_chat_name_context():
    _CHAT_NAME_CTX.chat_id = 0
    _CHAT_NAME_CTX.force_standard = False

class chat_name_context:
    def __init__(self, chat_id: int = 0, *, force_standard: bool = False):
        self.chat_id = int(chat_id or 0)
        self.force_standard = bool(force_standard)
        self.prev_chat_id = 0
        self.prev_force_standard = False

    def __enter__(self):
        self.prev_chat_id = _chat_name_ctx_chat_id()
        self.prev_force_standard = _chat_name_ctx_force_standard()
        set_chat_name_context(self.chat_id, force_standard=self.force_standard)
        return self

    def __exit__(self, exc_type, exc, tb):
        set_chat_name_context(self.prev_chat_id, force_standard=self.prev_force_standard)
        return False

def _normalize_chat_user_name(name: str) -> str:
    return str(name or "").replace("\r", " ").replace("\n", " ").strip()

def get_chat_user_name(chat_id: int, user_id: int) -> str:
    if int(chat_id or 0) == 0 or int(user_id or 0) == 0:
        return ""
    row = db_one(
        "SELECT display_name FROM chat_user_names WHERE chat_id=? AND user_id=? LIMIT 1",
        (int(chat_id), int(user_id))
    )
    if not row:
        return ""
    return (row["display_name"] or "").strip()

def set_chat_user_name(chat_id: int, user_id: int, name: str):
    nm = _normalize_chat_user_name(name)
    ts = int(now_ts())
    db_exec(
        "INSERT INTO chat_user_names(chat_id, user_id, display_name, created_at, updated_at) "
        "VALUES (?,?,?,?,?) "
        "ON CONFLICT(chat_id, user_id) DO UPDATE SET "
        "display_name=excluded.display_name, updated_at=excluded.updated_at",
        (int(chat_id), int(user_id), nm, ts, ts),
        commit=True
    )

def clear_chat_user_name(chat_id: int, user_id: int):
    db_exec(
        "DELETE FROM chat_user_names WHERE chat_id=? AND user_id=?",
        (int(chat_id), int(user_id)),
        commit=True
    )

def clear_all_chat_user_names_for_user(user_id: int):
    db_exec(
        "DELETE FROM chat_user_names WHERE user_id=?",
        (int(user_id),),
        commit=True
    )

def _chat_user_name_is_invalid(name: str) -> bool:
    nm = _normalize_chat_user_name(name)
    if not nm:
        return True
    if len(nm) > _CHAT_USER_NAME_MAX_LEN:
        return True
    return _is_transparent_or_zalgo_only_name(nm)

def standard_display_name(first_name: str, last_name: str, username: str, user_id: int) -> str:
    full = _strip_invisible(((first_name or "").strip() + " " + (last_name or "").strip())).strip()
    if full and (not _is_bad_single_char_name(full)) and (not _is_decorative_only_name(full)):
        return full

    un = _strip_invisible(username or "")
    if un:
        return un

    return str(int(user_id))

def display_name(first_name: str, last_name: str, username: str, user_id: int) -> str:
    base = standard_display_name(first_name, last_name, username, user_id)

    if _chat_name_ctx_force_standard():
        return base

    chat_id = _chat_name_ctx_chat_id()
    if chat_id != 0:
        alias = get_chat_user_name(chat_id, int(user_id))
        if alias:
            return alias

    return base

def user_full_name(u) -> str:
    return display_name(
        getattr(u, "first_name", "") or "",
        getattr(u, "last_name", "") or "",
        getattr(u, "username", "") or "",
        int(getattr(u, "id", 0) or 0),
    )

def _normalize_username_for_link(username: str) -> str:
    u = _strip_invisible(username or "").strip().lstrip("@")
    if not u:
        return ""
    u = re.sub(r"[^A-Za-z0-9_]", "", u)
    return u

def tg_mention(user_id: int, name: str, username: Optional[str] = None) -> str:
    uid = int(user_id)

    un = _normalize_username_for_link(username or "")
    if not un:
        try:
            row = db_one("SELECT username FROM users WHERE user_id=? LIMIT 1", (uid,))
            if row:
                un = _normalize_username_for_link((row["username"] or ""))
        except Exception:
            un = ""

    if un:
        href = f"https://t.me/{un}"
    else:
        href = f"tg://openmessage?user_id={uid}"

    return f'<a href="{href}">{h(name)}</a>'

def _ikb(text: str, *, callback_data: str = None, url: str = None, style: str = None) -> InlineKeyboardButton:
    kwargs = {}
    if callback_data is not None:
        kwargs["callback_data"] = callback_data
    if url is not None:
        kwargs["url"] = url
    if style:
        kwargs["style"] = style
    return InlineKeyboardButton(text, **kwargs)

_REAL_BOT_SEND_MESSAGE = bot.send_message
_REAL_BOT_REPLY_TO = bot.reply_to
_REAL_BOT_EDIT_MESSAGE_TEXT = bot.edit_message_text
_REAL_BOT_SEND_PHOTO = bot.send_photo
_REAL_BOT_SEND_VIDEO = bot.send_video

def _premium_text_payload(value):
    if isinstance(value, str):
        if "<tg-emoji" in value:
            return value
        return premiumize_html_text(value)
    return value

def _premiumize_caption_kwargs(kwargs: dict) -> dict:
    if "caption" in kwargs and isinstance(kwargs.get("caption"), str):
        kwargs["caption"] = premiumize_html_text(kwargs["caption"])
    return kwargs

def _is_send_text_forbidden_error(exc: Exception) -> bool:
    s = str(exc or "").lower()
    return (
        "not enough rights to send text messages to the chat" in s
        or "have no rights to send a message" in s
        or "chat_write_forbidden" in s
    )

def _is_chat_not_found_error(exc: Exception) -> bool:
    s = str(exc or "").lower()
    return "chat not found" in s

def _is_transient_telegram_network_error(exc: Exception) -> bool:
    s = str(exc or "").lower()
    return (
        "network is unreachable" in s
        or "failed to establish a new connection" in s
        or "max retries exceeded" in s
        or "connectionerror" in s
        or "read timed out" in s
        or "connect timeout" in s
        or "remotedisconnected" in s
        or "remote end closed connection without response" in s
        or "too many requests" in s
        or "retry after" in s
        or "error code: 429" in s
    )

def _try_send_result_to_pm_from_message(message, text, *args, **kwargs):
    try:
        u = getattr(message, "from_user", None)
        if not u or not getattr(u, "id", None):
            return None

        pm_kwargs = dict(kwargs)
        pm_kwargs.pop("reply_parameters", None)
        pm_kwargs.pop("reply_to_message_id", None)

        msg = _REAL_BOT_SEND_MESSAGE(
            int(u.id),
            _premium_text_payload(text),
            *args,
            **pm_kwargs
        )
        remember_bot_message_for_autodelete(msg)
        return msg
    except Exception:
        return None

def _bot_send_message_premium(chat_id, text, *args, **kwargs):
    msg = _REAL_BOT_SEND_MESSAGE(chat_id, _premium_text_payload(text), *args, **kwargs)
    remember_bot_message_for_autodelete(msg)
    return msg

def _bot_reply_to_premium(message, text, *args, **kwargs):
    try:
        send_kwargs = dict(kwargs)

        if "reply_parameters" in send_kwargs:
            send_kwargs.pop("reply_parameters", None)

        if "reply_to_message_id" not in send_kwargs:
            mid = int(getattr(message, "message_id", 0) or 0)
            if mid > 0:
                send_kwargs["reply_to_message_id"] = mid

        msg = _REAL_BOT_SEND_MESSAGE(
            int(message.chat.id),
            _premium_text_payload(text),
            *args,
            **send_kwargs
        )
        remember_reply_pair_for_autodelete(msg, message)
        return msg

    except Exception as e:
        chat_type = (getattr(getattr(message, "chat", None), "type", "") or "").lower()

        if chat_type in ("group", "supergroup") and _is_send_text_forbidden_error(e):
            pm_msg = _try_send_result_to_pm_from_message(message, text, *args, **kwargs)
            if pm_msg is not None:
                remember_reply_pair_for_autodelete(pm_msg, message)
                return pm_msg
            return None

        if _is_transient_telegram_network_error(e):
            return None

        raise

def _bot_edit_message_text_premium(text, *args, **kwargs):
    return _REAL_BOT_EDIT_MESSAGE_TEXT(_premium_text_payload(text), *args, **kwargs)

def _bot_send_photo_premium(chat_id, photo, *args, **kwargs):
    kwargs = _premiumize_caption_kwargs(kwargs)
    msg = _REAL_BOT_SEND_PHOTO(chat_id, photo, *args, **kwargs)
    remember_bot_message_for_autodelete(msg)
    return msg

def _bot_send_video_premium(chat_id, video, *args, **kwargs):
    kwargs = _premiumize_caption_kwargs(kwargs)
    msg = _REAL_BOT_SEND_VIDEO(chat_id, video, *args, **kwargs)
    remember_bot_message_for_autodelete(msg)
    return msg

bot.send_message = _bot_send_message_premium
bot.reply_to = _bot_reply_to_premium
bot.edit_message_text = _bot_edit_message_text_premium
bot.send_photo = _bot_send_photo_premium
bot.send_video = _bot_send_video_premium

def _file_sig(path: str) -> dict:
    try:
        st = os.stat(path)
        return {
            "exists": 1,
            "size": int(st.st_size),
            "mtime_ns": int(st.st_mtime_ns),
        }
    except Exception:
        return {
            "exists": 0,
            "size": 0,
            "mtime_ns": 0,
        }

def _old_main_db_signature() -> dict:
    return {
        "db": _file_sig(OLD_DB_PATH),
        "wal": _file_sig(OLD_DB_WAL_PATH),
    }

def _load_old_db_import_marker() -> dict:
    try:
        with open(OLD_DB_IMPORT_MARKER_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _save_old_db_import_marker(data: dict):
    try:
        with open(OLD_DB_IMPORT_MARKER_PATH, "w", encoding="utf-8") as f:
            json.dump(data or {}, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

def _q_ident(name: str) -> str:
    return '"' + str(name or "").replace('"', '""') + '"'

def _sqlite_integrity_ok_local(c: sqlite3.Connection) -> bool:
    try:
        row = c.execute("PRAGMA integrity_check;").fetchone()
        return bool(row and str(row[0]).strip().lower() == "ok")
    except Exception:
        return False

def _current_db_looks_populated() -> bool:
    try:
        r = conn.execute("SELECT COUNT(*) AS c FROM users").fetchone()
        if r and int(r[0] or 0) > 0:
            return True
    except Exception:
        pass

    try:
        r = conn.execute("SELECT COUNT(*) AS c FROM labs").fetchone()
        if r and int(r[0] or 0) > 0:
            return True
    except Exception:
        pass

    return False

def _copy_sqlite_db_snapshot(src_db_path: str, dst_snapshot_path: str):
    if os.path.exists(dst_snapshot_path):
        try:
            os.remove(dst_snapshot_path)
        except Exception:
            pass

    src_conn = sqlite3.connect(src_db_path, check_same_thread=False)
    try:
        src_conn.row_factory = sqlite3.Row
        src_conn.execute("PRAGMA busy_timeout=8000;")

        snap_conn = sqlite3.connect(dst_snapshot_path, check_same_thread=False)
        try:
            src_conn.backup(snap_conn)
            snap_conn.commit()
        finally:
            try:
                snap_conn.close()
            except Exception:
                pass
    finally:
        try:
            src_conn.close()
        except Exception:
            pass

def _import_sqlite_snapshot_into_current(snapshot_path: str) -> list[str]:
    imported_tables: list[str] = []

    with DB_LOCK:
        attached = False
        try:
            try:
                conn.execute("DETACH DATABASE old_import")
            except Exception:
                pass

            conn.execute("ATTACH DATABASE ? AS old_import", (snapshot_path,))
            attached = True

            old_tables = [
                r[0]
                for r in conn.execute(
                    "SELECT name FROM old_import.sqlite_master "
                    "WHERE type='table' AND name NOT LIKE 'sqlite_%' "
                    "ORDER BY name ASC"
                ).fetchall()
            ]

            cur_tables = {
                r[0]
                for r in conn.execute(
                    "SELECT name FROM main.sqlite_master "
                    "WHERE type='table' AND name NOT LIKE 'sqlite_%'"
                ).fetchall()
            }

            conn.execute("BEGIN")

            for table in old_tables:
                if table not in cur_tables:
                    continue

                old_cols = [
                    r[1]
                    for r in conn.execute(f"PRAGMA old_import.table_info({_q_ident(table)})").fetchall()
                ]
                cur_cols = {
                    r[1]
                    for r in conn.execute(f"PRAGMA main.table_info({_q_ident(table)})").fetchall()
                }

                cols = [c for c in old_cols if c in cur_cols]
                if not cols:
                    continue

                col_sql = ", ".join(_q_ident(c) for c in cols)

                conn.execute(
                    f"INSERT OR REPLACE INTO main.{_q_ident(table)} ({col_sql}) "
                    f"SELECT {col_sql} FROM old_import.{_q_ident(table)}"
                )
                imported_tables.append(str(table))

            try:
                for table in imported_tables:
                    row = conn.execute(
                        f"SELECT MAX(rowid) AS mx FROM main.{_q_ident(table)}"
                    ).fetchone()
                    mx = int(row[0] or 0) if row else 0
                    if mx > 0:
                        conn.execute(
                            "INSERT INTO sqlite_sequence(name, seq) VALUES (?, ?) "
                            "ON CONFLICT(name) DO UPDATE SET seq=excluded.seq",
                            (str(table), int(mx))
                        )
            except Exception:
                pass

            conn.commit()

        except Exception:
            try:
                conn.rollback()
            except Exception:
                pass
            raise
        finally:
            if attached:
                try:
                    conn.execute("DETACH DATABASE old_import")
                except Exception:
                    pass

    return imported_tables

def migrate_old_main_db_if_needed() -> bool:
    if not os.path.exists(OLD_DB_PATH):
        return False

    old_sig = _old_main_db_signature()
    marker = _load_old_db_import_marker()

    if marker.get("main") == old_sig and _current_db_looks_populated():
        return False

    snapshot_path = os.path.join(DATA_DIR, "_old_bio_war_import_snapshot.db")

    try:
        _copy_sqlite_db_snapshot(OLD_DB_PATH, snapshot_path)

        snap_conn = sqlite3.connect(snapshot_path, check_same_thread=False)
        try:
            if not _sqlite_integrity_ok_local(snap_conn):
                raise RuntimeError("integrity_check failed for old_data/bio_war.db snapshot")
        finally:
            try:
                snap_conn.close()
            except Exception:
                pass

        imported_tables = _import_sqlite_snapshot_into_current(snapshot_path)

        marker["main"] = old_sig
        marker["main_tables"] = list(imported_tables)
        marker["main_imported_at"] = int(now_ts())
        _save_old_db_import_marker(marker)

        return bool(imported_tables)

    finally:
        try:
            if os.path.exists(snapshot_path):
                os.remove(snapshot_path)
        except Exception:
            pass

# DB LAYER
def _sqlite_file_integrity_ok(path: str) -> bool:
    if not path or not os.path.exists(path):
        return False

    c = None
    try:
        c = sqlite3.connect(path, check_same_thread=False)
        c.row_factory = sqlite3.Row
        try:
            c.execute("PRAGMA busy_timeout=4000;")
        except Exception:
            pass

        row = c.execute("PRAGMA integrity_check;").fetchone()
        return bool(row and str(row[0]).strip().lower() == "ok")
    except Exception:
        return False
    finally:
        try:
            if c is not None:
                c.close()
        except Exception:
            pass

def _backup_name_for_existing_file(path: str, tag: str) -> str:
    ts = int(time.time())
    base = f"{path}.{tag}.{ts}.bak"
    cand = base
    n = 1
    while os.path.exists(cand):
        cand = f"{base}.{n}"
        n += 1
    return cand

def _rename_if_exists(path: str, tag: str) -> str:
    if not path or not os.path.exists(path):
        return ""
    new_path = _backup_name_for_existing_file(path, tag)
    os.replace(path, new_path)
    return new_path

def _sqlite_backup_file(src_path: str, dst_path: str) -> bool:
    if not os.path.exists(src_path):
        return False

    src = None
    dst = None
    try:
        os.makedirs(os.path.dirname(dst_path), exist_ok=True)

        src = sqlite3.connect(src_path, check_same_thread=False)
        src.row_factory = sqlite3.Row

        try:
            src.execute("PRAGMA busy_timeout=8000;")
            src.execute("PRAGMA wal_checkpoint(TRUNCATE);")
        except Exception:
            pass

        if os.path.exists(dst_path):
            try:
                os.remove(dst_path)
            except Exception:
                pass

        dst = sqlite3.connect(dst_path, check_same_thread=False)
        src.backup(dst)
        dst.commit()

        return _sqlite_file_integrity_ok(dst_path)
    except Exception:
        return False
    finally:
        try:
            if dst is not None:
                dst.close()
        except Exception:
            pass
        try:
            if src is not None:
                src.close()
        except Exception:
            pass

def _maybe_import_legacy_sqlite(src_path: str, dst_path: str, *, force: bool = False, label: str = "db") -> bool:
    if not os.path.exists(src_path):
        return False

    if not _sqlite_file_integrity_ok(src_path):
        return False

    dst_exists = os.path.exists(dst_path)
    dst_ok = _sqlite_file_integrity_ok(dst_path) if dst_exists else False

    need_import = bool(force or (not dst_exists) or (not dst_ok))
    if not need_import:
        return False

    try:
        if dst_exists:
            _rename_if_exists(dst_path, f"{label}_preimport")
        _rename_if_exists(dst_path + "-wal", f"{label}_preimport")
        _rename_if_exists(dst_path + "-shm", f"{label}_preimport")
    except Exception:
        pass

    return _sqlite_backup_file(src_path, dst_path)

def _bootstrap_legacy_databases():
    force = bool(FORCE_IMPORT_OLD_DB)

    try:
        _maybe_import_legacy_sqlite(
            LEGACY_DB_PATH,
            DB_PATH,
            force=force,
            label="main"
        )
    except Exception:
        pass

    try:
        _maybe_import_legacy_sqlite(
            LEGACY_DELETED_DB_PATH,
            DELETED_DB_PATH,
            force=force,
            label="deleted"
        )
    except Exception:
        pass

_bootstrap_legacy_databases()

conn = sqlite3.connect(DB_PATH, check_same_thread=False)
conn.row_factory = sqlite3.Row
conn.execute("PRAGMA journal_mode=WAL;")
conn.execute("PRAGMA synchronous=NORMAL;")
conn.execute("PRAGMA busy_timeout=8000;")
conn.execute("PRAGMA wal_autocheckpoint=256;")   # ~1MB при page_size=4096

_DB_COMMITS_SINCE_CKPT = 0

def db_one(sql: str, params=()):
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute(sql, params)
            return c.fetchone()
        finally:
            try: c.close()
            except Exception: pass

def db_all(sql: str, params=()):
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute(sql, params)
            return c.fetchall()
        finally:
            try: c.close()
            except Exception: pass

def db_exec(sql: str, params=(), commit: bool = False):
    global _DB_COMMITS_SINCE_CKPT

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute(sql, params)
            rc = c.rowcount
            if commit:
                conn.commit()
                _DB_COMMITS_SINCE_CKPT += 1

                if _DB_COMMITS_SINCE_CKPT >= 40:
                    try:
                        conn.execute("PRAGMA wal_checkpoint(PASSIVE);")
                    except Exception:
                        pass
                    _DB_COMMITS_SINCE_CKPT = 0

            return rc
        finally:
            try:
                c.close()
            except Exception:
                pass

def table_exists(name: str) -> bool:
    try:
        r = db_one("SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1", (str(name),))
        return bool(r)
    except Exception:
        return False

# демоны
DB_CKPT_PASSIVE_EVERY_SEC = 60
DB_CKPT_TRUNCATE_EVERY_SEC = 600
DB_CKPT_NEXT_PASSIVE_TS = int(now_ts() + DB_CKPT_PASSIVE_EVERY_SEC)
DB_CKPT_NEXT_TRUNCATE_TS = int(now_ts() + DB_CKPT_TRUNCATE_EVERY_SEC)

def _checkpoint_daemon():
    global DB_CKPT_NEXT_PASSIVE_TS, DB_CKPT_NEXT_TRUNCATE_TS

    tick = 0
    while True:
        time.sleep(DB_CKPT_PASSIVE_EVERY_SEC)
        tick += 1

        with DB_LOCK:
            try:
                conn.execute("PRAGMA wal_checkpoint(PASSIVE);")
            except Exception:
                pass

            DB_CKPT_NEXT_PASSIVE_TS = int(now_ts() + DB_CKPT_PASSIVE_EVERY_SEC)

            if tick % 10 == 0:
                try:
                    conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
                except Exception:
                    pass
                DB_CKPT_NEXT_TRUNCATE_TS = int(now_ts() + DB_CKPT_TRUNCATE_EVERY_SEC)

threading.Thread(target=_checkpoint_daemon, daemon=True).start()

def _infection_daemon():
    while True:
        try:
            now = now_ts()
            if (not table_exists("infections")):
                time.sleep(2)
                continue            

            rows = db_all(
                "SELECT attacker_id, target_id, add_bio_res, end_ts, next_payout_ts "
                "FROM infections WHERE next_payout_ts>0 AND next_payout_ts<=? AND end_ts>?",
                (now, now)
            ) or []

            for r in rows:
                att = int(r["attacker_id"])
                tgt = int(r["target_id"])
                add = int(r["add_bio_res"] or 0)
                if add > 0:
                    db_exec(
                        "UPDATE labs SET all_bio_res=COALESCE(all_bio_res,0)+? WHERE user_id=?",
                        (add, att),
                        commit=True
                    )
                nxt = int(r["next_payout_ts"] or 0) + 86400
                end_ts = int(r["end_ts"] or 0)
                if nxt >= end_ts:
                    nxt = 0
                db_exec(
                    "UPDATE infections SET next_payout_ts=? WHERE attacker_id=? AND target_id=?",
                    (int(nxt), att, tgt),
                    commit=True
                )

            exp = db_all(
                "SELECT attacker_id, target_id, counted FROM infections WHERE end_ts<=?",
                (now,)
            ) or []

            for r in exp:
                att = int(r["attacker_id"])
                tgt = int(r["target_id"])
                counted = int(r["counted"] or 0)

                if counted == 1:
                    db_exec(
                        "UPDATE labs SET infected_total=CASE WHEN COALESCE(infected_total,0)>0 THEN infected_total-1 ELSE 0 END "
                        "WHERE user_id=?",
                        (att,),
                        commit=True
                    )
                    db_exec(
                        "UPDATE labs SET diseases_total=CASE WHEN COALESCE(diseases_total,0)>0 THEN diseases_total-1 ELSE 0 END "
                        "WHERE user_id=?",
                        (tgt,),
                        commit=True
                    )

                db_exec("DELETE FROM infections WHERE attacker_id=? AND target_id=?", (att, tgt), commit=True)

        except Exception as e:
            send_error_report("_infection_daemon", e)

        time.sleep(15)

PATHOGEN_CRAFT_SEC = 3 * 3600 # время крафта патогена
VACCINE_CRAFT_SEC = 9 * 3600  # время крафта вакцины

# демоны изготовления
def _pathogen_factory_daemon():
    while True:
        try:
            now = now_ts()
            rows = db_all(
                "SELECT user_id, COALESCE(ready_pathogens,0) AS r, COALESCE(total_pathogens,0) AS t, "
                "COALESCE(next_pathogen_in,0) AS n, COALESCE(next_pathogen_last_ts,0) AS last, COALESCE(acceleration,0) AS acc FROM labs"
            ) or []

            for row in rows:
                uid = int(row["user_id"])
                ready = int(row["r"])
                total = int(row["t"])
                nxt = int(row["n"])
                last = int(row["last"])
                acc = int(row["acc"] if row else 0)
                craft_sec, dup_pct = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, acc)

                if total <= 0:
                    continue

                if last <= 0:
                    db_exec("UPDATE labs SET next_pathogen_last_ts=? WHERE user_id=?", (now, uid), commit=True)
                    continue

                elapsed = now - last
                if elapsed <= 0:
                    continue

                if ready >= total:
                    if nxt != 0:
                        db_exec(
                            "UPDATE labs SET next_pathogen_in=0, next_pathogen_last_ts=? WHERE user_id=?",
                            (now, uid),
                            commit=True
                        )
                    else:
                        db_exec("UPDATE labs SET next_pathogen_last_ts=? WHERE user_id=?", (now, uid), commit=True)
                    continue

                if nxt <= 0 and ready < total:
                    nxt = craft_sec
                    elapsed = 0 

                while elapsed > 0 and ready < total:
                    if elapsed >= nxt:
                        elapsed -= nxt
                        produced = 1 + (1 if _roll_pct(dup_pct) else 0)
                        ready += produced
                        if ready > total:
                            ready = total
                        if ready >= total:
                            nxt = 0
                            break
                        nxt = craft_sec
                    else:
                        nxt -= elapsed
                        elapsed = 0
                                
                db_exec(
                    "UPDATE labs SET ready_pathogens=?, next_pathogen_in=?, next_pathogen_last_ts=? WHERE user_id=?",
                    (ready, nxt, now, uid),
                    commit=True
                )

        except Exception as e:
            send_error_report("_pathogen_factory_daemon", e)

        time.sleep(5)

def _vaccine_factory_daemon():
    while True:
        try:
            now = now_ts()
            rows = db_all(
                "SELECT user_id, COALESCE(ready_vaccines,0) AS r, COALESCE(total_vaccines,0) AS t, "
                "COALESCE(next_vaccine_in,0) AS n, COALESCE(next_vaccine_last_ts,0) AS last, COALESCE(acceleration,0) AS acc FROM labs"
            ) or []

            for row in rows:
                uid = int(row["user_id"])
                ready = int(row["r"])
                total = int(row["t"])
                nxt = int(row["n"])
                last = int(row["last"])
                acc = int(row["acc"] if row else 0)
                craft_sec, dup_pct = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, acc)

                if total <= 0:
                    continue

                if last <= 0:
                    db_exec("UPDATE labs SET next_vaccine_last_ts=? WHERE user_id=?", (now, uid), commit=True)
                    continue

                elapsed = now - last
                if elapsed <= 0:
                    continue

                if ready >= total:
                    if nxt != 0:
                        db_exec(
                            "UPDATE labs SET next_vaccine_in=0, next_vaccine_last_ts=? WHERE user_id=?",
                            (now, uid),
                            commit=True
                        )
                    else:
                        db_exec("UPDATE labs SET next_vaccine_last_ts=? WHERE user_id=?", (now, uid), commit=True)
                    continue

                if nxt <= 0 and ready < total:
                    nxt = craft_sec
                    elapsed = 0

                while elapsed > 0 and ready < total:
                    if elapsed >= nxt:
                        elapsed -= nxt
                        produced = 1 + (1 if _roll_pct(dup_pct) else 0)
                        ready += produced
                        if ready > total:
                            ready = total
                        if ready >= total:
                            nxt = 0
                            break
                        nxt = craft_sec
                    else:
                        nxt -= elapsed
                        elapsed = 0

                db_exec(
                    "UPDATE labs SET ready_vaccines=?, next_vaccine_in=?, next_vaccine_last_ts=? WHERE user_id=?",
                    (ready, nxt, now, uid),
                    commit=True
                )

        except Exception as e:
            send_error_report("_vaccine_factory_daemon", e)

        time.sleep(5)

# демон чистки
def _housekeeping_daemon():
    while True:
        try:
            now = now_ts()

            try:
                _maybe_promote_unavailable_creator(force=False)
            except Exception as e:
                send_error_report("_maybe_promote_unavailable_creator", e)

            db_exec(
                "UPDATE autoanswer_state "
                "SET used=0, reset_at=?, waiting_no_pathogens=0, waiting_since=0, waiting_hot=0, waiting_hot_since=0 "
                "WHERE enabled=1 AND reset_at>0 AND reset_at<=?",
                (int(now + 86400), int(now)),
                commit=True
            )

            exp_requests = db_all(
                "SELECT request_id FROM corp_requests "
                "WHERE status='pending' AND expires_at<=? "
                "ORDER BY request_id ASC",
                (int(now),)
            ) or []
            for r in exp_requests:
                try:
                    _corp_request_expire(int(r["request_id"]))
                except Exception as e:
                    send_error_report("_corp_request_expire", e)

            exp_invites = db_all(
                "SELECT invite_id FROM corp_invites "
                "WHERE status='pending' AND expires_at<=? "
                "ORDER BY invite_id ASC",
                (int(now),)
            ) or []
            for r in exp_invites:
                try:
                    _corp_invite_expire(int(r["invite_id"]))
                except Exception as e:
                    send_error_report("_corp_invite_expire", e)

            try:
                _duel_housekeeping_once(int(now))
            except Exception as e:
                send_error_report("_duel_housekeeping_once", e)

            purge_deleted_db(now)
            _run_due_timers(now)
            run_chat_autodelete_once()
            _run_db_file_msg_once(int(now))

        except Exception as e:
            send_error_report("_tz3_housekeeping_daemon", e)

        time.sleep(60)

# DB
def init_db():
    db_exec("""
    CREATE TABLE IF NOT EXISTS users (
        user_id            INTEGER PRIMARY KEY,
        username           TEXT,
        first_name         TEXT,
        last_name          TEXT,
        notify_chat_id     INTEGER DEFAULT 0,
        notify_off         INTEGER DEFAULT 0,
        last_seen          INTEGER DEFAULT 0,
        is_placeholder     INTEGER DEFAULT 0,
        is_bot             INTEGER DEFAULT 0,
        bot_status_locked  INTEGER DEFAULT 0,
        rp_off             INTEGER DEFAULT 0,
        gender             TEXT NOT NULL DEFAULT 'male'
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS support_agents (
        user_id     INTEGER PRIMARY KEY,
        role        TEXT NOT NULL DEFAULT 'support',
        added_by    INTEGER,
        added_at    INTEGER
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS bot_creator (
        slot_id              INTEGER PRIMARY KEY CHECK(slot_id=1),
        user_id              INTEGER NOT NULL,
        updated_at           INTEGER NOT NULL DEFAULT 0,
        promoted_from_owner  INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS bot_owners (
        user_id     INTEGER PRIMARY KEY,
        added_by    INTEGER NOT NULL DEFAULT 0,
        added_at    INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS bot_bans (
        user_id      INTEGER PRIMARY KEY,
        banned_by    INTEGER,
        banned_at    INTEGER NOT NULL,
        until_ts     INTEGER NOT NULL DEFAULT 0,
        reason       TEXT DEFAULT '',
        username     TEXT DEFAULT '',
        first_name   TEXT DEFAULT '',
        last_name    TEXT DEFAULT ''
    );
    """, commit=True)

    for sql in (
        "ALTER TABLE bot_bans ADD COLUMN username TEXT DEFAULT ''",
        "ALTER TABLE bot_bans ADD COLUMN first_name TEXT DEFAULT ''",
        "ALTER TABLE bot_bans ADD COLUMN last_name TEXT DEFAULT ''",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS lab_delete_pending (
        user_id     INTEGER PRIMARY KEY,
        created_at  INTEGER NOT NULL
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS autoanswer_state (
        user_id      INTEGER PRIMARY KEY,
        enabled      INTEGER NOT NULL DEFAULT 0,
        enabled_at   INTEGER NOT NULL DEFAULT 0,
        reset_at     INTEGER NOT NULL DEFAULT 0,
        used         INTEGER NOT NULL DEFAULT 0,
        waiting_no_pathogens INTEGER NOT NULL DEFAULT 0,
        waiting_since INTEGER NOT NULL DEFAULT 0,
        last_warn_ts INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    # миграции autoanswer_state
    for sql in (
        "ALTER TABLE autoanswer_state ADD COLUMN waiting_hot INTEGER DEFAULT 0",
        "ALTER TABLE autoanswer_state ADD COLUMN waiting_hot_since INTEGER DEFAULT 0",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS autoanswer_used_reports (
        user_id   INTEGER NOT NULL,
        chat_id   INTEGER NOT NULL,
        msg_id    INTEGER NOT NULL,
        ts        INTEGER NOT NULL,
        PRIMARY KEY(user_id, chat_id, msg_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS sabotage_cooldowns (
        attacker_id INTEGER NOT NULL,
        target_id   INTEGER NOT NULL,
        until_ts    INTEGER NOT NULL,
        PRIMARY KEY(attacker_id, target_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS corps (
        corp_id      INTEGER PRIMARY KEY AUTOINCREMENT,
        name         TEXT NOT NULL UNIQUE,
        owner_id     INTEGER NOT NULL,
        created_chat_id INTEGER NOT NULL DEFAULT 0,
        created_at   INTEGER NOT NULL,
        is_open      INTEGER NOT NULL DEFAULT 1,
        min_bio_exp  INTEGER NOT NULL DEFAULT 0,
        description  TEXT NOT NULL DEFAULT ''
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS corp_members (
        corp_id    INTEGER NOT NULL,
        user_id    INTEGER NOT NULL,
        role       TEXT NOT NULL DEFAULT 'member',  -- owner|deputy|member
        joined_at  INTEGER NOT NULL,
        PRIMARY KEY(corp_id, user_id)
    );
    """, commit=True)

    try:
        db_exec("CREATE UNIQUE INDEX IF NOT EXISTS ux_corp_members_user ON corp_members(user_id);", commit=True)
    except Exception:
        pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS corp_invites (
        invite_id   INTEGER PRIMARY KEY AUTOINCREMENT,
        corp_id     INTEGER NOT NULL,
        user_id     INTEGER NOT NULL,
        invited_by  INTEGER NOT NULL,
        created_at  INTEGER NOT NULL,
        expires_at  INTEGER NOT NULL,
        status      TEXT NOT NULL DEFAULT 'pending',   -- pending|accepted|declined|expired
        chat_id     INTEGER NOT NULL DEFAULT 0,
        msg_id      INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS corp_requests (
        request_id  INTEGER PRIMARY KEY AUTOINCREMENT,
        corp_id     INTEGER NOT NULL,
        user_id     INTEGER NOT NULL,
        created_at  INTEGER NOT NULL,
        expires_at  INTEGER NOT NULL,
        status      TEXT NOT NULL DEFAULT 'pending'    -- pending|approved|rejected|expired
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS corp_request_msgs (
        request_id  INTEGER NOT NULL,
        chat_id     INTEGER NOT NULL,
        msg_id      INTEGER NOT NULL,
        kind        TEXT NOT NULL DEFAULT 'other', -- owner|deputy|user|group|other
        PRIMARY KEY(request_id, chat_id, msg_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS corp_notify_prefs (
        user_id    INTEGER PRIMARY KEY,
        enabled    INTEGER NOT NULL DEFAULT 1
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS duel_invites (
        invite_id      INTEGER PRIMARY KEY AUTOINCREMENT,
        chat_id        INTEGER NOT NULL,
        challenger_id  INTEGER NOT NULL,
        target_id      INTEGER NOT NULL,
        stake_amount   INTEGER NOT NULL DEFAULT 0,
        created_at     INTEGER NOT NULL DEFAULT 0,
        expires_at     INTEGER NOT NULL DEFAULT 0,
        status         TEXT NOT NULL DEFAULT 'pending', -- pending|accepted|declined|expired|superseded|cancelled
        msg_chat_id    INTEGER NOT NULL DEFAULT 0,
        msg_id         INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS duels (
        duel_id              INTEGER PRIMARY KEY AUTOINCREMENT,
        invite_id            INTEGER NOT NULL DEFAULT 0,
        chat_id              INTEGER NOT NULL,
        challenger_id        INTEGER NOT NULL,
        target_id            INTEGER NOT NULL,
        stake_amount         INTEGER NOT NULL DEFAULT 0,
        started_at           INTEGER NOT NULL DEFAULT 0,
        next_action_until    INTEGER NOT NULL DEFAULT 0,
        current_turn_user_id INTEGER NOT NULL DEFAULT 0,
        turns_done           INTEGER NOT NULL DEFAULT 0,
        challenger_aim_bonus INTEGER NOT NULL DEFAULT 0,
        target_aim_bonus     INTEGER NOT NULL DEFAULT 0,
        status               TEXT NOT NULL DEFAULT 'active', -- active|finished|cancelled|draw
        winner_id            INTEGER NOT NULL DEFAULT 0,
        loser_id             INTEGER NOT NULL DEFAULT 0,
        msg_chat_id          INTEGER NOT NULL DEFAULT 0,
        msg_id               INTEGER NOT NULL DEFAULT 0,
        ended_at             INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS duel_bets (
        bet_id         INTEGER PRIMARY KEY AUTOINCREMENT,
        duel_id        INTEGER NOT NULL,
        chat_id        INTEGER NOT NULL,
        bettor_id      INTEGER NOT NULL,
        candidate_id   INTEGER NOT NULL,
        amount         INTEGER NOT NULL DEFAULT 0,
        created_at     INTEGER NOT NULL DEFAULT 0,
        status         TEXT NOT NULL DEFAULT 'active' -- active|paid|refunded|lost
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS duel_stats (
        user_id             INTEGER PRIMARY KEY,
        wins                INTEGER NOT NULL DEFAULT 0,
        draws               INTEGER NOT NULL DEFAULT 0,
        losses              INTEGER NOT NULL DEFAULT 0,
        max_win_materials   INTEGER NOT NULL DEFAULT 0,
        max_lose_materials  INTEGER NOT NULL DEFAULT 0,
        win_streak          INTEGER NOT NULL DEFAULT 0,
        best_win_streak     INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_duel_invites_target_chat ON duel_invites(chat_id, target_id, status, invite_id DESC);", commit=True)
    except Exception:
        pass

    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_duel_invites_challenger_chat ON duel_invites(chat_id, challenger_id, status, invite_id DESC);", commit=True)
    except Exception:
        pass

    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_duels_chat_status ON duels(chat_id, status, duel_id DESC);", commit=True)
    except Exception:
        pass

    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_duel_bets_duel ON duel_bets(duel_id, candidate_id, status);", commit=True)
    except Exception:
        pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS report_state (
        user_id     INTEGER PRIMARY KEY,
        category    TEXT NOT NULL DEFAULT '',
        stage       TEXT NOT NULL DEFAULT '',
        created_ts  INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS balance_chain_state (
        user_id            INTEGER PRIMARY KEY,
        chain_kind         TEXT NOT NULL DEFAULT '',
        button_text        TEXT NOT NULL DEFAULT '',
        payload_json       TEXT NOT NULL DEFAULT '',
        source_chat_id     INTEGER NOT NULL DEFAULT 0,
        source_message_id  INTEGER NOT NULL DEFAULT 0,
        updated_at         INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS quick_infect_prefs (
        user_id       INTEGER PRIMARY KEY,
        mode          TEXT NOT NULL DEFAULT 'r',
        chat_filter   TEXT NOT NULL DEFAULT 'n',
        updated_at    INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS user_timers (
        timer_id       INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id        INTEGER NOT NULL,
        chat_id        INTEGER NOT NULL DEFAULT 0,
        created_at     INTEGER NOT NULL DEFAULT 0,
        next_run_ts    INTEGER NOT NULL DEFAULT 0,
        is_cycle       INTEGER NOT NULL DEFAULT 0,
        repeat_spec    TEXT NOT NULL DEFAULT '',
        cycle_total    INTEGER NOT NULL DEFAULT 0,
        cycle_left     INTEGER NOT NULL DEFAULT 0,
        command_text   TEXT NOT NULL DEFAULT ''
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS db_file_msg_schedule (
        user_id       INTEGER PRIMARY KEY,
        repeat_spec   TEXT NOT NULL DEFAULT '',
        next_run_ts   INTEGER NOT NULL DEFAULT 0,
        updated_at    INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS db_file_exports (
        db_id         INTEGER PRIMARY KEY AUTOINCREMENT,
        source_kind   TEXT NOT NULL DEFAULT '',
        archive_path  TEXT NOT NULL DEFAULT '',
        requested_by  INTEGER NOT NULL DEFAULT 0,
        created_at    INTEGER NOT NULL DEFAULT 0,
        request_text  TEXT NOT NULL DEFAULT ''
    );
    """, commit=True)

    for sql in (
        "ALTER TABLE user_timers ADD COLUMN chat_id INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_timers ADD COLUMN cycle_total INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_timers ADD COLUMN cycle_left INTEGER NOT NULL DEFAULT 0",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    try:
        db_exec(
            "UPDATE user_timers SET cycle_total=2, cycle_left=2 "
            "WHERE is_cycle=1 AND (COALESCE(cycle_total,0)=0 OR COALESCE(cycle_left,0)=0)",
            commit=True
        )
    except Exception:
        pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS user_name_restrictions (
        user_id            INTEGER PRIMARY KEY,
        user_locked        INTEGER NOT NULL DEFAULT 0,
        user_by            INTEGER NOT NULL DEFAULT 0,
        user_at            INTEGER NOT NULL DEFAULT 0,
        user_reason        TEXT NOT NULL DEFAULT '',
        lab_locked         INTEGER NOT NULL DEFAULT 0,
        lab_by             INTEGER NOT NULL DEFAULT 0,
        lab_at             INTEGER NOT NULL DEFAULT 0,
        lab_reason         TEXT NOT NULL DEFAULT '',
        pat_locked         INTEGER NOT NULL DEFAULT 0,
        pat_by             INTEGER NOT NULL DEFAULT 0,
        pat_at             INTEGER NOT NULL DEFAULT 0,
        pat_reason         TEXT NOT NULL DEFAULT '',
        corp_locked        INTEGER NOT NULL DEFAULT 0,
        corp_by            INTEGER NOT NULL DEFAULT 0,
        corp_at            INTEGER NOT NULL DEFAULT 0,
        corp_reason        TEXT NOT NULL DEFAULT ''
    );
    """, commit=True)

    for sql in (
        "ALTER TABLE user_name_restrictions ADD COLUMN user_locked INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN user_by INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN user_at INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN user_reason TEXT NOT NULL DEFAULT ''",
        "ALTER TABLE user_name_restrictions ADD COLUMN corp_locked INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN corp_by INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN corp_at INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE user_name_restrictions ADD COLUMN corp_reason TEXT NOT NULL DEFAULT ''",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS chat_user_names (
        chat_id       INTEGER NOT NULL,
        user_id       INTEGER NOT NULL,
        display_name  TEXT NOT NULL DEFAULT '',
        created_at    INTEGER NOT NULL DEFAULT 0,
        updated_at    INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY (chat_id, user_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS labs (
        user_id         INTEGER PRIMARY KEY,
        lab_name        TEXT,
        pathogen_name   TEXT,
        corp_name       TEXT,
        corp_id         INTEGER DEFAULT 0,

        ready_pathogens INTEGER DEFAULT 1,
        total_pathogens INTEGER DEFAULT 1,
        next_pathogen_in INTEGER DEFAULT 10800,
        ready_vaccines INTEGER DEFAULT 1,
        total_vaccines INTEGER DEFAULT 1,
        next_vaccine_in INTEGER DEFAULT 32400,
                
        qualification   INTEGER DEFAULT 1,
        synthesis     INTEGER DEFAULT 1,
        acceleration     INTEGER DEFAULT 1,

        security        INTEGER DEFAULT 1,
        reaction        INTEGER DEFAULT 1,
        ids             INTEGER DEFAULT 1,
        ips             INTEGER DEFAULT 1,

        infectivity     INTEGER DEFAULT 1,
        lethality       INTEGER DEFAULT 1,
        immunity        INTEGER DEFAULT 1,
        heaviness        INTEGER DEFAULT 1,

        bio_exp         INTEGER DEFAULT 0,
        bio_res         INTEGER DEFAULT 0,

        all_bio_res     INTEGER DEFAULT 0,
        all_bio_mater   INTEGER DEFAULT 0,
        last_synth_ts   INTEGER DEFAULT 0,

        fever_until_ts  INTEGER DEFAULT 0,
        fever_pathogen       TEXT DEFAULT '',
        next_pathogen_last_ts INTEGER DEFAULT 0,
        next_vaccine_last_ts INTEGER DEFAULT 0,
        ops_total       INTEGER DEFAULT 0,

        hide_balance    INTEGER DEFAULT 0,
        hide_lab        INTEGER DEFAULT 0,
        lab_active     INTEGER DEFAULT 0,       

        successful_ops  INTEGER DEFAULT 0,
        prevented_ops   INTEGER DEFAULT 0,
        defended_total  INTEGER DEFAULT 0,

        infected_total  INTEGER DEFAULT 0,
        diseases_total  INTEGER DEFAULT 0
    );
    """, commit=True)

    try:
        db_exec("ALTER TABLE labs ADD COLUMN skill_points INTEGER DEFAULT 0", commit=True)
    except Exception:
        pass

    # промокоды
    db_exec("""
    CREATE TABLE IF NOT EXISTS promo_codes (
        promo_id        INTEGER PRIMARY KEY AUTOINCREMENT,
        code            TEXT NOT NULL,
        code_key        TEXT NOT NULL UNIQUE,
        is_permanent    INTEGER NOT NULL DEFAULT 0,
        expires_ts      INTEGER NOT NULL DEFAULT 0,
        created_at      INTEGER NOT NULL DEFAULT 0,
        created_by      INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS promo_bonuses (
        bonus_id        INTEGER PRIMARY KEY AUTOINCREMENT,
        promo_id        INTEGER NOT NULL,
        kind            TEXT NOT NULL,
        ref_code        TEXT NOT NULL DEFAULT '',
        amount          INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS promo_uses (
        promo_id        INTEGER NOT NULL,
        user_id         INTEGER NOT NULL,
        used_at         INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY (promo_id, user_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS infect_formula_settings (
        settings_id   INTEGER PRIMARY KEY CHECK(settings_id=1),
        k_value       REAL NOT NULL DEFAULT 0.5,
        beta_value    REAL NOT NULL DEFAULT 1.0,
        updated_at    INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)
    
    db_exec(
        "INSERT OR IGNORE INTO infect_formula_settings(settings_id, k_value, beta_value, updated_at) VALUES (1,?,?,?)",
        (float(INFECT_BOUND_K), float(INFECT_BOUND_BETA), int(now_ts())),
        commit=True
    )

    db_exec("""
    CREATE TABLE IF NOT EXISTS duel_formula_settings (
        settings_id      INTEGER PRIMARY KEY CHECK(settings_id=1),
        rounds_value     INTEGER NOT NULL DEFAULT 40,
        base_hit_pct     INTEGER NOT NULL DEFAULT 20,
        aim_step_pct     INTEGER NOT NULL DEFAULT 8,
        break_base_pct   INTEGER NOT NULL DEFAULT 22,
        break_step_pct   INTEGER NOT NULL DEFAULT 8,
        updated_at       INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec(
        "INSERT OR IGNORE INTO duel_formula_settings("
        "settings_id, rounds_value, base_hit_pct, aim_step_pct, break_base_pct, break_step_pct, updated_at"
        ") VALUES (1,?,?,?,?,?,?)",
        (
            int(DUEL_MAX_TURNS),
            int(DUEL_BASE_HIT_PCT),
            int(DUEL_AIM_STEP_PCT),
            int(DUEL_BREAK_BASE_PCT),
            int(DUEL_BREAK_STEP_PCT),
            int(now_ts())
        ),
        commit=True
    )

    # автоудаление
    db_exec("""
    CREATE TABLE IF NOT EXISTS chat_auto_delete (
        chat_id        INTEGER PRIMARY KEY,
        ttl_seconds    INTEGER NOT NULL DEFAULT 0,
        updated_by     INTEGER NOT NULL DEFAULT 0,
        updated_at     INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS bot_sent_messages (
        chat_id        INTEGER NOT NULL,
        message_id     INTEGER NOT NULL,
        sent_at        INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY (chat_id, message_id)
    );
    """, commit=True)

    # миграции users
    for sql in (
        "ALTER TABLE users ADD COLUMN notify_chat_id INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN pm_opened INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN notify_off INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN is_placeholder INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN is_bot INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN bot_status_locked INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN rp_off INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN gender TEXT NOT NULL DEFAULT 'male'",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    # миграции лаб
    for sql in (
        "ALTER TABLE labs ADD COLUMN all_bio_res INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN all_bio_mater INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN last_synth_ts INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN fever_until_ts INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN fever_pathogen TEXT DEFAULT ''",
        "ALTER TABLE labs ADD COLUMN next_pathogen_last_ts INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN ready_vaccines INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN total_vaccines INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN next_vaccine_in INTEGER DEFAULT 32400",
        "ALTER TABLE labs ADD COLUMN next_vaccine_last_ts INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN ops_total INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN hide_balance INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN hide_lab INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN lab_active INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN reaction INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN ids INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN ips INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN synthesis INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN acceleration INTEGER DEFAULT 1",
        "ALTER TABLE labs ADD COLUMN defended_total INTEGER DEFAULT 0",
        "ALTER TABLE labs ADD COLUMN corp_id INTEGER DEFAULT 0",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS infection_seen (
        attacker_id INTEGER NOT NULL,
        target_id   INTEGER NOT NULL,
        first_ts    INTEGER NOT NULL,
        PRIMARY KEY(attacker_id, target_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS infection_cooldowns (
        attacker_id INTEGER NOT NULL,
        target_id   INTEGER NOT NULL,
        until_ts    INTEGER NOT NULL,
        PRIMARY KEY(attacker_id, target_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS infection_fail_stacks (
        attacker_id  INTEGER NOT NULL,
        target_id    INTEGER NOT NULL,
        fail_count   INTEGER NOT NULL DEFAULT 0,
        last_fail_ts INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY(attacker_id, target_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS infections (
        attacker_id     INTEGER NOT NULL,
        target_id       INTEGER NOT NULL,
        start_ts        INTEGER NOT NULL,
        end_ts          INTEGER NOT NULL,
        add_bio_res     INTEGER NOT NULL DEFAULT 1,
        next_payout_ts  INTEGER NOT NULL DEFAULT 0,
        counted         INTEGER NOT NULL DEFAULT 1,
        PRIMARY KEY(attacker_id, target_id)
    );
    """, commit=True)

    try:
        db_exec("ALTER TABLE infections ADD COLUMN pathogen_name TEXT DEFAULT ''", commit=True)
    except Exception:
        pass

    try:
        db_exec("ALTER TABLE infections ADD COLUMN known_to_target INTEGER DEFAULT 0", commit=True)
    except Exception:
        pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS chat_members (
        chat_id   INTEGER NOT NULL,
        user_id   INTEGER NOT NULL,
        username  TEXT,
        last_seen INTEGER NOT NULL,
        PRIMARY KEY(chat_id, user_id)
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS bot_group_chats (
        chat_id      INTEGER PRIMARY KEY,
        title        TEXT NOT NULL DEFAULT '',
        chat_type    TEXT NOT NULL DEFAULT '',
        is_active    INTEGER NOT NULL DEFAULT 1,
        updated_at   INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    try:
        db_exec("ALTER TABLE bot_group_chats ADD COLUMN owner_id INTEGER DEFAULT 0", commit=True)
    except Exception:
        pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS rp_offers (
        offer_id     INTEGER PRIMARY KEY AUTOINCREMENT,
        actor_id     INTEGER NOT NULL,
        action_key   TEXT NOT NULL,
        target_id    INTEGER NOT NULL DEFAULT 0,
        status       TEXT NOT NULL DEFAULT 'pending',
        created_at   INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    for sql in (
        "ALTER TABLE rp_offers ADD COLUMN extra_tail TEXT NOT NULL DEFAULT ''",
        "ALTER TABLE rp_offers ADD COLUMN comment_text TEXT NOT NULL DEFAULT ''",
    ):
        try:
            db_exec(sql, commit=True)
        except Exception:
            pass

    db_exec("""
    CREATE TABLE IF NOT EXISTS rp_events (
        event_id      INTEGER PRIMARY KEY AUTOINCREMENT,
        action_key    TEXT NOT NULL,
        actor_id      INTEGER NOT NULL,
        target_id     INTEGER NOT NULL,
        created_at    INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec("""
    CREATE TABLE IF NOT EXISTS personal_rp_actions (
        action_id      INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id        INTEGER NOT NULL,
        trigger        TEXT NOT NULL,
        trigger_key    TEXT NOT NULL,
        emoji          TEXT NOT NULL DEFAULT '',
        premium_id     TEXT NOT NULL DEFAULT '',
        action_text    TEXT NOT NULL,
        uses_count     INTEGER NOT NULL DEFAULT 0,
        created_at     INTEGER NOT NULL DEFAULT 0
    );
    """, commit=True)

    db_exec(
        "CREATE INDEX IF NOT EXISTS idx_personal_rp_user ON personal_rp_actions(user_id, action_id);",
        commit=True
    )
    db_exec(
        "CREATE UNIQUE INDEX IF NOT EXISTS idx_personal_rp_user_trigger ON personal_rp_actions(user_id, trigger_key);",
        commit=True
    )

    # индексы для топов/болезней
    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_infections_target_end ON infections(target_id, end_ts);", commit=True)
    except Exception:
        pass
    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_infections_end ON infections(end_ts);", commit=True)
    except Exception:
        pass

    # корпорации
    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_corps_chat ON corps(created_chat_id);", commit=True)
    except Exception:
        pass
    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_corp_invites_user ON corp_invites(user_id, status, expires_at);", commit=True)
    except Exception:
        pass
    try:
        db_exec("CREATE INDEX IF NOT EXISTS idx_corp_requests_user ON corp_requests(user_id, status, expires_at);", commit=True)
    except Exception:
        pass

    # миграции
    try:
        db_exec("ALTER TABLE chat_members ADD COLUMN username TEXT", commit=True)
    except Exception:
        pass

    try:
        db_exec(
            "UPDATE labs SET next_pathogen_in=10800 WHERE COALESCE(next_pathogen_last_ts,0)=0 AND next_pathogen_in=3600",
            commit=True
        )
    except Exception:
        pass

    load_infect_formula_settings()
    load_duel_formula_settings()

def init_deleted_db(): # отдельная БД для удалённых лабораторий
    conn2 = sqlite3.connect(DELETED_DB_PATH, check_same_thread=False)
    conn2.row_factory = sqlite3.Row
    try:
        conn2.execute("PRAGMA journal_mode=WAL;")
        conn2.execute("PRAGMA synchronous=NORMAL;")
        conn2.execute("PRAGMA temp_store=MEMORY;")
    except Exception:
        pass

    conn2.execute("""
    CREATE TABLE IF NOT EXISTS deleted_labs (
        user_id     INTEGER PRIMARY KEY,
        deleted_at  INTEGER NOT NULL,
        purge_at    INTEGER NOT NULL,
        snapshot_json TEXT NOT NULL DEFAULT '',
        meta_json     TEXT NOT NULL DEFAULT ''
    );
    """)

    conn2.execute("""
    CREATE TABLE IF NOT EXISTS deleted_labs_log (
        id         INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id    INTEGER NOT NULL,
        ts         INTEGER NOT NULL,
        action     TEXT NOT NULL,
        payload    TEXT NOT NULL DEFAULT ''
    );
    """)

    try:
        conn2.execute("CREATE INDEX IF NOT EXISTS idx_deleted_labs_purge ON deleted_labs(purge_at);")
    except Exception:
        pass

    conn2.commit()
    conn2.close()

def purge_deleted_db(now: int):
    try:
        conn2 = sqlite3.connect(DELETED_DB_PATH, check_same_thread=False)
        conn2.row_factory = sqlite3.Row
        conn2.execute("DELETE FROM deleted_labs WHERE purge_at<=?", (int(now),))
        conn2.commit()
        conn2.close()
    except Exception:
        pass

def _deleted_db_one(sql: str, params=()):
    conn2 = sqlite3.connect(DELETED_DB_PATH, check_same_thread=False)
    conn2.row_factory = sqlite3.Row
    try:
        c = conn2.cursor()
        c.execute(sql, params)
        row = c.fetchone()
        c.close()
        return row
    finally:
        conn2.close()

def _deleted_db_exec(sql: str, params=(), *, commit: bool = False):
    conn2 = sqlite3.connect(DELETED_DB_PATH, check_same_thread=False)
    conn2.row_factory = sqlite3.Row
    try:
        c = conn2.cursor()
        c.execute(sql, params)
        rc = c.rowcount
        if commit:
            conn2.commit()
        c.close()
        return rc
    finally:
        conn2.close()

def _deleted_lab_log(user_id: int, action: str, payload: str = ""):
    try:
        _deleted_db_exec(
            "INSERT INTO deleted_labs_log(user_id, ts, action, payload) VALUES (?,?,?,?)",
            (int(user_id), int(now_ts()), str(action), str(payload or "")),
            commit=True
        )
    except Exception:
        pass

def get_deleted_lab_row(user_id: int):
    return _deleted_db_one(
        "SELECT user_id, deleted_at, purge_at, snapshot_json, meta_json "
        "FROM deleted_labs WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )

def save_deleted_lab_snapshot(user_id: int, snapshot: dict, meta: dict):
    init_deleted_db()
    now = now_ts()
    purge_at = int(now + 30 * 86400)
    _deleted_db_exec(
        "INSERT OR REPLACE INTO deleted_labs(user_id, deleted_at, purge_at, snapshot_json, meta_json) "
        "VALUES (?,?,?,?,?)",
        (
            int(user_id),
            int(now),
            int(purge_at),
            json.dumps(snapshot, ensure_ascii=False),
            json.dumps(meta, ensure_ascii=False),
        ),
        commit=True
    )
    _deleted_lab_log(int(user_id), "save", f"purge_at={purge_at}")

def delete_deleted_lab_snapshot(user_id: int):
    _deleted_db_exec("DELETE FROM deleted_labs WHERE user_id=?", (int(user_id),), commit=True)
    _deleted_lab_log(int(user_id), "remove")

def _load_deleted_meta(row) -> dict:
    try:
        return json.loads((row["meta_json"] or "") or "{}") if row else {}
    except Exception:
        return {}

def _save_deleted_meta(user_id: int, meta: dict):
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return
    _deleted_db_exec(
        "UPDATE deleted_labs SET meta_json=? WHERE user_id=?",
        (json.dumps(meta or {}, ensure_ascii=False), int(user_id)),
        commit=True
    )

def _maybe_apply_deleted_lab_bonus(user_id: int):
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return

    meta = _load_deleted_meta(row)
    if int(meta.get("grant_applied", 0) or 0) == 1:
        return

    grant = int(meta.get("granted_bio_mater", 0) or 0)
    if grant <= 0:
        return

    ensure_lab_exists(int(user_id))
    db_exec(
        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? WHERE user_id=?",
        (int(grant), int(user_id)),
        commit=True
    )

    meta["grant_applied"] = 1
    meta["grant_applied_at"] = int(now_ts())
    _save_deleted_meta(int(user_id), meta)
    _deleted_lab_log(int(user_id), "grant_bonus", f"+{grant}")

def set_lab_delete_pending(user_id: int):
    db_exec(
        "INSERT INTO lab_delete_pending(user_id, created_at) VALUES (?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET created_at=excluded.created_at",
        (int(user_id), int(now_ts())),
        commit=True
    )

def clear_lab_delete_pending(user_id: int):
    db_exec("DELETE FROM lab_delete_pending WHERE user_id=?", (int(user_id),), commit=True)

def has_lab_delete_pending(user_id: int) -> bool:
    r = db_one("SELECT 1 FROM lab_delete_pending WHERE user_id=? LIMIT 1", (int(user_id),))
    return r is not None

def _bot_pm_link_html() -> str:
    if BOT_USERNAME:
        return f'<a href="https://t.me/{h(BOT_USERNAME)}">личных сообщениях</a>'
    return "личных сообщениях"

def _bot_pm_url() -> str:
    if BOT_USERNAME:
        return f"https://t.me/{BOT_USERNAME}"
    return ""

def kb_open_bot_pm() -> Optional[InlineKeyboardMarkup]:
    url = _bot_pm_url()
    if not url:
        return None
    kb = InlineKeyboardMarkup()
    kb.add(_ikb("Перейти в личные сообщения", url=url, style="success"))
    return kb

def _send_hidden_self_info_to_pm(viewer_id: int, text: str, reply_markup=None) -> bool:
    try:
        bot.send_message(
            int(viewer_id),
            text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=reply_markup
        )
        return True
    except Exception:
        return False

def build_lab_delete_confirm_text() -> str:
    return (
        "⚠️ Вы собираетесь удалить свою Лабораторию.\n\n"
        "После удаления у Вас будет всего 3 дня для её восстановления.\n\n"
        f"Если вы точно уверены в своём решении, введите <code>{h(LAB_DELETE_PHRASE)}</code>"
    )

def build_lab_deleted_text() -> str:
    return (
        "❎ Вы исключили себя из участия в мини-игре «Био-атака»\n\n"
        "💬 У Вас есть 3 дня на восстановление Лаборатории. "
        "Команда \"<code>Био восстановить лабу</code>\"\n"
        f"Для отслеживания состояния лаборатории перейдите в {_bot_pm_link_html()}"
    )

def kb_lab_delete_confirm(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        _ikb("Да, подтверждаю", callback_data=f"{CB_LAB_DELETE_OK}:{int(uid)}", style="danger"),
        _ikb("Отмена", callback_data=f"{CB_LAB_DELETE_CANCEL}:{int(uid)}", style="success")
    )
    return kb

def _deleted_lab_restore_offer_mode(user_id: int) -> str:
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return ""

    meta = _load_deleted_meta(row)
    if int(meta.get("suppress_restore_offer", 0) or 0) == 1:
        return ""

    now = now_ts()
    deleted_at = int(row["deleted_at"] or 0)
    purge_at = int(row["purge_at"] or 0)
    self_until = int(deleted_at + 3 * 86400)

    if now <= self_until:
        return "SELF"
    if now <= purge_at:
        return "SUPPORT"
    return ""

def _set_deleted_lab_restore_offer_suppressed(user_id: int, suppressed: bool = True):
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return

    meta = _load_deleted_meta(row)
    meta["suppress_restore_offer"] = 1 if suppressed else 0
    meta["suppress_restore_offer_at"] = int(now_ts()) if suppressed else 0
    _save_deleted_meta(int(user_id), meta)

def build_inactive_lab_text(user_id: int, *, after_delete: bool = False) -> str:
    base = build_lab_deleted_text() if after_delete else "📑 У вас нет активной Лаборатории."
    mode = _deleted_lab_restore_offer_mode(int(user_id))

    if mode == "SELF":
        return (
            f"{base}\n\n"
            "Вы можете создать новую лабораторию или восстановить ранее удалённую."
        )

    if mode == "SUPPORT":
        return (
            f"{base}\n\n"
            "Срок самовосстановления истёк.\n"
            "Вы можете создать новую лабораторию или запросить восстановление через техподдержку."
        )

    return base

def kb_inactive_lab_actions(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    mode = _deleted_lab_restore_offer_mode(int(uid))

    if mode == "SELF":
        kb.row(
            _ikb("Создать лабу", callback_data=f"{CB_LAB_CREATE}:{int(uid)}", style="success"),
            _ikb("Восстановить лабу", callback_data=f"{CB_LAB_RESTORE}:{int(uid)}", style="primary")
        )
        return kb

    if mode == "SUPPORT":
        kb.row(
            _ikb("Создать лабу", callback_data=f"{CB_LAB_CREATE}:{int(uid)}", style="success"),
            _ikb("Запросить восстановление", callback_data=f"{CB_LAB_RESTORE_REQ}:{int(uid)}", style="primary")
        )
        return kb

    kb.add(_ikb("Создать лабу", callback_data=f"{CB_LAB_CREATE}:{int(uid)}", style="success"))
    return kb

def _lab_state_edit_current(cq, text: str, rm=None):
    if getattr(cq, "inline_message_id", None):
        limited_edit_message_text(
            text=text,
            inline_id=cq.inline_message_id,
            parse_mode="HTML",
            reply_markup=rm,
            disable_web_page_preview=True
        )
    elif getattr(cq, "message", None):
        limited_edit_message_text(
            text=text,
            chat_id=int(cq.message.chat.id),
            msg_id=int(cq.message.message_id),
            parse_mode="HTML",
            reply_markup=rm,
            disable_web_page_preview=True
        )

def _start_restore_report_flow_for_user(user_id: int) -> tuple[bool, str]:
    uid = int(user_id)
    report_clear_state(uid)
    report_set_state(uid, "RESTORE", "await_content")
    prompt = _report_prompt(uid, "RESTORE")

    try:
        bot.send_message(
            uid,
            prompt,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return True, "🔁 Запрос переведён в личные сообщения бота."
    except Exception:
        report_clear_state(uid)
        return False, "📑 Не удалось открыть личные сообщения. Сначала откройте личный чат с ботом."

def _row_to_dict(row):
    return dict(row) if row else None

def _rows_to_dicts(rows):
    return [dict(r) for r in (rows or [])]

def _corp_transfer_on_lab_delete(user_id: int):
    cid, _ = get_user_corp_resolved(int(user_id))
    if int(cid) <= 0:
        return

    role = corp_role(int(cid), int(user_id))
    if role != "owner":
        db_exec("DELETE FROM corp_members WHERE corp_id=? AND user_id=?", (int(cid), int(user_id)), commit=True)
        db_exec("UPDATE labs SET corp_id=0, corp_name='' WHERE user_id=?", (int(user_id),), commit=True)
        return

    rep = db_one(
        "SELECT user_id FROM corp_members "
        "WHERE corp_id=? AND user_id<>? AND role='deputy' "
        "ORDER BY joined_at ASC LIMIT 1",
        (int(cid), int(user_id))
    )
    if not rep:
        rep = db_one(
            "SELECT user_id FROM corp_members "
            "WHERE corp_id=? AND user_id<>? AND role='member' "
            "ORDER BY joined_at ASC LIMIT 1",
            (int(cid), int(user_id))
        )

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            if rep:
                new_owner_id = int(rep["user_id"])
                c.execute("UPDATE corps SET owner_id=? WHERE corp_id=?", (new_owner_id, int(cid)))
                c.execute("UPDATE corp_members SET role='owner' WHERE corp_id=? AND user_id=?", (int(cid), new_owner_id))
                c.execute("DELETE FROM corp_members WHERE corp_id=? AND user_id=?", (int(cid), int(user_id)))
            else:
                reqs = db_all("SELECT request_id FROM corp_requests WHERE corp_id=?", (int(cid),)) or []
                for r in reqs:
                    c.execute("DELETE FROM corp_request_msgs WHERE request_id=?", (int(r["request_id"]),))
                c.execute("DELETE FROM corp_requests WHERE corp_id=?", (int(cid),))
                c.execute("DELETE FROM corp_invites WHERE corp_id=?", (int(cid),))
                c.execute("DELETE FROM corp_members WHERE corp_id=?", (int(cid),))
                c.execute("DELETE FROM corps WHERE corp_id=?", (int(cid),))

            c.execute("UPDATE labs SET corp_id=0, corp_name='' WHERE user_id=?", (int(user_id),))
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _build_deleted_lab_snapshot(user_id: int) -> tuple[dict, dict]:
    lab = db_one("SELECT * FROM labs WHERE user_id=?", (int(user_id),))
    corp_meta = db_one(
        "SELECT m.corp_id, m.user_id, m.role, m.joined_at, c.name "
        "FROM corp_members m "
        "JOIN corps c ON c.corp_id=m.corp_id "
        "WHERE m.user_id=? LIMIT 1",
        (int(user_id),)
    )

    snapshot = {
        "lab": _row_to_dict(lab),
        "corp_member": _row_to_dict(corp_meta),
        "infections_out": _rows_to_dicts(db_all("SELECT * FROM infections WHERE attacker_id=?", (int(user_id),))),
        "infections_in": _rows_to_dicts(db_all("SELECT * FROM infections WHERE target_id=?", (int(user_id),))),
        "infection_seen": _rows_to_dicts(
            db_all("SELECT * FROM infection_seen WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
        ),
        "infection_cooldowns": _rows_to_dicts(
            db_all("SELECT * FROM infection_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
        ),
        "sabotage_cooldowns": _rows_to_dicts(
            db_all("SELECT * FROM sabotage_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
        ),
    }

    lab_row = snapshot["lab"] or {}
    grant_mater = max(1, int(lab_row.get("all_bio_res", 0) or 0) // 2) if lab_row else 0
    meta = {
        "granted_bio_mater": int(grant_mater),
        "grant_applied": 0,
        "grant_applied_at": 0,
        "suppress_restore_offer": 0,
        "suppress_restore_offer_at": 0,
    }
    return snapshot, meta

def _perform_lab_delete(user_id: int) -> tuple[bool, str]:
    lab = db_one("SELECT * FROM labs WHERE user_id=?", (int(user_id),))
    if not lab or int(lab["lab_active"] or 0) != 1:
        clear_lab_delete_pending(int(user_id))
        return False, "📑 У вас нет активной Лаборатории."

    snapshot, meta = _build_deleted_lab_snapshot(int(user_id))
    save_deleted_lab_snapshot(int(user_id), snapshot, meta)

    out_rows = db_all("SELECT attacker_id, target_id, counted FROM infections WHERE attacker_id=?", (int(user_id),)) or []
    in_rows = db_all("SELECT attacker_id, target_id, counted FROM infections WHERE target_id=?", (int(user_id),)) or []

    try:
        _corp_transfer_on_lab_delete(int(user_id))

        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")

                for r in out_rows:
                    if int(r["counted"] or 0) == 1 and int(r["target_id"]) != int(user_id):
                        c.execute(
                            "UPDATE labs SET diseases_total=CASE WHEN COALESCE(diseases_total,0)>0 THEN diseases_total-1 ELSE 0 END "
                            "WHERE user_id=?",
                            (int(r["target_id"]),)
                        )

                for r in in_rows:
                    if int(r["counted"] or 0) == 1 and int(r["attacker_id"]) != int(user_id):
                        c.execute(
                            "UPDATE labs SET infected_total=CASE WHEN COALESCE(infected_total,0)>0 THEN infected_total-1 ELSE 0 END "
                            "WHERE user_id=?",
                            (int(r["attacker_id"]),)
                        )

                c.execute("DELETE FROM infections WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM infection_seen WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM infection_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM sabotage_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM autoanswer_used_reports WHERE user_id=?", (int(user_id),))
                c.execute("DELETE FROM autoanswer_state WHERE user_id=?", (int(user_id),))
                c.execute("DELETE FROM labs WHERE user_id=?", (int(user_id),))

                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        clear_lab_delete_pending(int(user_id))
        _deleted_lab_log(int(user_id), "delete", "ok")
        return True, build_lab_deleted_text()

    except Exception as e:
        send_error_report("_perform_lab_delete", e)
        return False, "📑 Не удалось удалить Лабораторию."

def _restore_deleted_lab(user_id: int, *, support_mode: bool = False) -> tuple[bool, str]:
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return False, "📑 У вас нет сохранённой Лаборатории для восстановления."

    now = now_ts()
    deleted_at = int(row["deleted_at"] or 0)
    if not support_mode and now > deleted_at + 3 * 86400:
        return False, "⚠️ Вы не можете восстановить свою лабораторию. Срок восстановления лаборатории истёк."

    try:
        snapshot = json.loads((row["snapshot_json"] or "") or "{}")
        _meta = json.loads((row["meta_json"] or "") or "{}")
        grant_mater = int((_meta or {}).get("granted_bio_mater", 0) or 0)
        grant_applied = int((_meta or {}).get("grant_applied", 0) or 0)
    except Exception:
        snapshot = {}
        _meta = {}

    lab_data = snapshot.get("lab") or {}
    if not lab_data:
        return False, "📑 Не удалось восстановить данные Лаборатории."

    corp_meta = snapshot.get("corp_member") or None
    inf_out = snapshot.get("infections_out") or []
    inf_in = snapshot.get("infections_in") or []
    seen_rows = snapshot.get("infection_seen") or []
    cd_rows = snapshot.get("infection_cooldowns") or []
    sab_rows = snapshot.get("sabotage_cooldowns") or []

    lab_data["corp_id"] = 0
    lab_data["corp_name"] = ""

    try:
        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")

                c.execute("DELETE FROM corp_members WHERE user_id=?", (int(user_id),))
                c.execute("DELETE FROM infections WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM infection_seen WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM infection_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM sabotage_cooldowns WHERE attacker_id=? OR target_id=?", (int(user_id), int(user_id)))
                c.execute("DELETE FROM labs WHERE user_id=?", (int(user_id),))

                cols = list(lab_data.keys())
                ph = ",".join(["?"] * len(cols))
                c.execute(
                    f"INSERT OR REPLACE INTO labs({','.join(cols)}) VALUES ({ph})",
                    tuple(lab_data[k] for k in cols)
                )
                if grant_applied == 1 and grant_mater > 0:
                    c.execute(
                        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)-? WHERE user_id=?",
                        (int(grant_mater), int(user_id))
                    )

                for r in inf_out:
                    cols = list(r.keys())
                    ph = ",".join(["?"] * len(cols))
                    c.execute(
                        f"INSERT OR REPLACE INTO infections({','.join(cols)}) VALUES ({ph})",
                        tuple(r[k] for k in cols)
                    )
                    if int(r.get("counted", 0) or 0) == 1 and int(r.get("target_id", 0) or 0) != int(user_id):
                        c.execute(
                            "UPDATE labs SET diseases_total=COALESCE(diseases_total,0)+1 WHERE user_id=?",
                            (int(r["target_id"]),)
                        )

                for r in inf_in:
                    cols = list(r.keys())
                    ph = ",".join(["?"] * len(cols))
                    c.execute(
                        f"INSERT OR REPLACE INTO infections({','.join(cols)}) VALUES ({ph})",
                        tuple(r[k] for k in cols)
                    )
                    if int(r.get("counted", 0) or 0) == 1 and int(r.get("attacker_id", 0) or 0) != int(user_id):
                        c.execute(
                            "UPDATE labs SET infected_total=COALESCE(infected_total,0)+1 WHERE user_id=?",
                            (int(r["attacker_id"]),)
                        )

                for r in seen_rows:
                    cols = list(r.keys())
                    ph = ",".join(["?"] * len(cols))
                    c.execute(
                        f"INSERT OR REPLACE INTO infection_seen({','.join(cols)}) VALUES ({ph})",
                        tuple(r[k] for k in cols)
                    )

                for r in cd_rows:
                    cols = list(r.keys())
                    ph = ",".join(["?"] * len(cols))
                    c.execute(
                        f"INSERT OR REPLACE INTO infection_cooldowns({','.join(cols)}) VALUES ({ph})",
                        tuple(r[k] for k in cols)
                    )

                for r in sab_rows:
                    cols = list(r.keys())
                    ph = ",".join(["?"] * len(cols))
                    c.execute(
                        f"INSERT OR REPLACE INTO sabotage_cooldowns({','.join(cols)}) VALUES ({ph})",
                        tuple(r[k] for k in cols)
                    )

                if corp_meta:
                    corp = corp_by_id(int(corp_meta.get("corp_id", 0) or 0))
                    if corp:
                        restored_role = str(corp_meta.get("role", "member") or "member")
                        if restored_role == "owner":
                            restored_role = "member"

                        c.execute(
                            "INSERT OR REPLACE INTO corp_members(corp_id, user_id, role, joined_at) VALUES (?,?,?,?)",
                            (
                                int(corp["corp_id"]),
                                int(user_id),
                                restored_role,
                                int(corp_meta.get("joined_at", now) or now)
                            )
                        )
                        c.execute(
                            "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                            (int(corp["corp_id"]), (corp["name"] or "").strip(), int(user_id))
                        )

                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        delete_deleted_lab_snapshot(int(user_id))
        clear_lab_delete_pending(int(user_id))
        _deleted_lab_log(int(user_id), "restore", "ok")
        if grant_applied == 1 and grant_mater > 0:
            _deleted_lab_log(int(user_id), "restore_adjust", f"-{grant_mater}")
        return True, "✅ Лаборатория восстановлена."

    except Exception as e:
        send_error_report("_restore_deleted_lab", e)
        return False, "📑 Не удалось восстановить Лабораторию."

def upsert_user(tg_user):
    db_exec("""
        INSERT INTO users(
            user_id, username, first_name, last_name, last_seen,
            is_placeholder, is_bot, bot_status_locked
        )
        VALUES(?,?,?,?,?,?,?,0)
        ON CONFLICT(user_id) DO UPDATE SET
            username=excluded.username,
            first_name=excluded.first_name,
            last_name=excluded.last_name,
            last_seen=excluded.last_seen,
            is_placeholder=0,
            is_bot=CASE
                WHEN COALESCE(users.bot_status_locked,0)=1 THEN users.is_bot
                ELSE excluded.is_bot
            END
    """, (
        int(tg_user.id),
        (tg_user.username or "").lower() if tg_user.username else None,
        tg_user.first_name,
        tg_user.last_name,
        now_ts(),
        0,
        1 if bool(getattr(tg_user, "is_bot", False)) else 0
    ), commit=True)

def get_current_creator_id() -> int:
    row = db_one("SELECT user_id FROM bot_creator WHERE slot_id=1 LIMIT 1")
    try:
        uid = int(row["user_id"] or 0) if row else 0
    except Exception:
        uid = 0
    return uid if uid > 0 else int(CREATOR_ID)

def ensure_creator_role_state():
    row = db_one("SELECT user_id FROM bot_creator WHERE slot_id=1 LIMIT 1")
    try:
        current_uid = int(row["user_id"] or 0) if row else 0
    except Exception:
        current_uid = 0

    if current_uid <= 0:
        db_exec(
            "INSERT INTO bot_creator(slot_id, user_id, updated_at, promoted_from_owner) "
            "VALUES (1,?,?,0) "
            "ON CONFLICT(slot_id) DO UPDATE SET "
            "user_id=excluded.user_id, "
            "updated_at=excluded.updated_at, "
            "promoted_from_owner=excluded.promoted_from_owner",
            (int(CREATOR_ID), int(now_ts())),
            commit=True
        )

def get_bot_owners() -> List[sqlite3.Row]:
    return db_all("""
        SELECT bo.user_id, bo.added_by, bo.added_at,
               u.username, u.first_name, u.last_name, u.last_seen
        FROM bot_owners bo
        LEFT JOIN users u ON u.user_id = bo.user_id
        ORDER BY bo.added_at ASC, bo.user_id ASC
    """)

def is_creator(user_id: int) -> bool:
    return int(user_id) == int(get_current_creator_id())

def is_owner(user_id: int) -> bool:
    row = db_one("SELECT 1 FROM bot_owners WHERE user_id=? LIMIT 1", (int(user_id),))
    return bool(row)

def is_agent(user_id: int) -> bool:
    uid = int(user_id)
    if is_creator(uid) or is_owner(uid):
        return False
    row = db_one("SELECT 1 FROM support_agents WHERE user_id=? LIMIT 1", (uid,))
    return bool(row)

def can_use_owner_commands(user_id: int) -> bool:
    return is_owner(int(user_id))

def can_manage_owners(user_id: int) -> bool:
    return is_creator(int(user_id))

def can_manage_agents(user_id: int) -> bool:
    return is_owner(int(user_id))

def add_bot_owner(target_id: int, added_by: int) -> None:
    db_exec("""
        INSERT INTO bot_owners(user_id, added_by, added_at)
        VALUES(?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            added_by=excluded.added_by,
            added_at=excluded.added_at
    """, (int(target_id), int(added_by), int(now_ts())), commit=True)

def remove_bot_owner(target_id: int) -> None:
    db_exec("DELETE FROM bot_owners WHERE user_id=?", (int(target_id),), commit=True)

def add_agent(target_id: int, added_by: int, role: str = "support") -> None:
    db_exec("""
        INSERT INTO support_agents(user_id, role, added_by, added_at)
        VALUES(?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            role=excluded.role,
            added_by=excluded.added_by,
            added_at=excluded.added_at
    """, (int(target_id), str(role or "support"), int(added_by), int(now_ts())), commit=True)

def remove_agent(target_id: int):
    db_exec("DELETE FROM support_agents WHERE user_id=?", (int(target_id),), commit=True)

def promote_next_owner_to_creator() -> Optional[int]:
    current_creator = int(get_current_creator_id())

    row = db_one(
        "SELECT user_id FROM bot_owners "
        "WHERE user_id<>? "
        "ORDER BY added_at ASC, user_id ASC "
        "LIMIT 1",
        (int(current_creator),)
    )
    if not row:
        return None

    new_creator_id = int(row["user_id"])
    db_exec(
        "INSERT INTO bot_creator(slot_id, user_id, updated_at, promoted_from_owner) "
        "VALUES (1,?,?,1) "
        "ON CONFLICT(slot_id) DO UPDATE SET "
        "user_id=excluded.user_id, "
        "updated_at=excluded.updated_at, "
        "promoted_from_owner=excluded.promoted_from_owner",
        (int(new_creator_id), int(now_ts())),
        commit=True
    )
    return int(new_creator_id)

# аварийная передача прав
CREATOR_AUDIT_INTERVAL_SEC = 6 * 3600
_CREATOR_AUDIT_NEXT_TS = 0

def _normalize_deleted_account_text(s: str) -> str:
    return re.sub(r"\s+", " ", _strip_invisible(s or "")).strip().casefold()

def _looks_like_deleted_account_profile(username: str, first_name: str, last_name: str) -> bool:
    un = _normalize_username_for_link(username or "")
    if un:
        return False

    first = _normalize_deleted_account_text(first_name or "")
    full = _normalize_deleted_account_text(f"{first_name or ''} {last_name or ''}")

    markers = {
        "deleted account",
        "удаленный аккаунт",
        "удалённый аккаунт",
    }
    return first in markers or full in markers

def _save_role_user_snapshot(user_id: int, username: str, first_name: str, last_name: str):
    db_exec(
        "INSERT INTO users(user_id, username, first_name, last_name, last_seen, is_placeholder, is_bot) "
        "VALUES(?,?,?,?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "username=excluded.username, "
        "first_name=excluded.first_name, "
        "last_name=excluded.last_name, "
        "last_seen=excluded.last_seen, "
        "is_placeholder=0",
        (
            int(user_id),
            (username or "").lower() if (username or "").strip() else None,
            (first_name or "").strip() or None,
            (last_name or "").strip() or None,
            int(now_ts()),
            0,
            0,
        ),
        commit=True
    )

def _is_creator_inaccessible_error(exc: Exception) -> bool:
    s = str(exc or "").lower()
    return (
        _is_chat_not_found_error(exc)
        or "private chat not found" in s
        or "user not found" in s
        or "user is deactivated" in s
        or "user_deactivated" in s
        or "bot was blocked by the user" in s
    )

def _creator_unavailable_reason(user_id: int) -> tuple[bool, str]:
    uid = int(user_id)

    row = get_user_row(uid)
    if row and _looks_like_deleted_account_profile(
        (row["username"] or ""),
        (row["first_name"] or ""),
        (row["last_name"] or "")
    ):
        return True, "deleted_profile_db"

    try:
        ch = bot.get_chat(uid)

        username = (getattr(ch, "username", "") or "").strip().lower()
        first_name = (
            getattr(ch, "first_name", None)
            or getattr(ch, "title", None)
            or ""
        )
        last_name = getattr(ch, "last_name", None) or ""

        _save_role_user_snapshot(uid, username, first_name, last_name)

        if _looks_like_deleted_account_profile(username, first_name, last_name):
            return True, "deleted_profile_api"

        return False, ""

    except Exception as e:
        if _is_transient_telegram_network_error(e):
            return False, ""
        if _is_creator_inaccessible_error(e):
            return True, str(e)
        return False, ""

def _role_user_tag(user_id: int) -> str:
    uid = int(user_id)
    row = get_user_row(uid)
    if not row:
        return f"<code>{uid}</code>"

    un = (row["username"] or "")
    disp = standard_display_name(
        row["first_name"] or "",
        row["last_name"] or "",
        un,
        uid
    )
    return tg_mention(uid, disp, username=un)

def _maybe_promote_unavailable_creator(force: bool = False) -> Optional[int]:
    global _CREATOR_AUDIT_NEXT_TS

    ensure_creator_role_state()

    now = int(now_ts())
    if not force and now < int(_CREATOR_AUDIT_NEXT_TS or 0):
        return None

    _CREATOR_AUDIT_NEXT_TS = int(now + CREATOR_AUDIT_INTERVAL_SEC)

    old_creator_id = int(get_current_creator_id())
    must_promote, reason = _creator_unavailable_reason(int(old_creator_id))
    if not must_promote:
        return None

    new_creator_id = promote_next_owner_to_creator()
    if not new_creator_id or int(new_creator_id) == int(old_creator_id):
        return None

    try:
        db_exec("DELETE FROM bot_owners WHERE user_id=?", (int(old_creator_id),), commit=True)
    except Exception:
        pass

    try:
        db_exec("DELETE FROM support_agents WHERE user_id=?", (int(old_creator_id),), commit=True)
    except Exception:
        pass

    ensure_creator_is_support()

    text = (
        "⚠️ Текущий создатель бота более недоступен для бота.\n"
        f"Новым создателем назначен {_role_user_tag(int(new_creator_id))}."
    )

    if str(reason or "").strip():
        text += f"\n📋 Причина: <code>{h(str(reason)[:300])}</code>"

    try:
        _send_message_to_service_recipients(
            text,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    except Exception:
        pass

    return int(new_creator_id)

def ensure_creator_is_support():
    """
    Совместимый bootstrap для старой логики.
    Пока старые handler'ы ещё не переведены на creator/owner/agent,
    оставляем creator в support_agents, чтобы ничего не сломать.
    """
    ensure_creator_role_state()

    creator_id = int(get_current_creator_id())
    db_exec("""
        INSERT INTO support_agents(user_id, role, added_by, added_at)
        VALUES(?,?,?,?)
        ON CONFLICT(user_id) DO NOTHING
    """, (creator_id, "support", creator_id, now_ts()), commit=True)

def ensure_lab_exists(user_id: int):
    uid = int(user_id)
    row = db_one("SELECT 1 FROM labs WHERE user_id=? LIMIT 1", (uid,))
    if not row:
        db_exec("INSERT INTO labs(user_id) VALUES(?)", (uid,), commit=True)

def mark_lab_active(user_id: int):
    ensure_lab_exists(user_id)
    db_exec("UPDATE labs SET lab_active=1 WHERE user_id=?", (int(user_id),), commit=True)

def is_lab_active(user_id: int) -> bool:
    r = db_one("SELECT COALESCE(lab_active,0) AS a FROM labs WHERE user_id=? LIMIT 1", (int(user_id),))
    return bool(r) and int(r["a"] or 0) == 1

def set_hide_balance(user_id: int, hide: bool):
    ensure_lab_exists(user_id)
    db_exec("UPDATE labs SET hide_balance=? WHERE user_id=?", (1 if hide else 0, int(user_id)), commit=True)

def set_hide_lab(user_id: int, hide: bool):
    ensure_lab_exists(user_id)
    db_exec("UPDATE labs SET hide_lab=? WHERE user_id=?", (1 if hide else 0, int(user_id)), commit=True)

def get_privacy_flags(user_id: int) -> tuple[int, int]:
    ensure_lab_exists(user_id)
    r = db_one("SELECT COALESCE(hide_balance,0) AS hb, COALESCE(hide_lab,0) AS hl FROM labs WHERE user_id=?", (int(user_id),))
    if not r:
        return 0, 0
    return int(r["hb"] or 0), int(r["hl"] or 0)

def get_user_corp(user_id: int) -> tuple[int, str]:
    """(corp_id, corp_name) из labs."""
    ensure_lab_exists(int(user_id))
    r = db_one("SELECT COALESCE(corp_id,0) AS cid, COALESCE(corp_name,'') AS cn FROM labs WHERE user_id=?",
               (int(user_id),))
    if not r:
        return 0, ""
    return int(r["cid"] or 0), (r["cn"] or "").strip()

def get_user_corp_resolved(user_id: int) -> tuple[int, str]:
    """
    Сначала берём корпорацию из labs.
    Если там пусто, пытаемся восстановить по corp_members и сразу синхронизируем labs.
    """
    cid, cname = get_user_corp(int(user_id))
    if cid > 0:
        return cid, cname

    r = db_one(
        "SELECT c.corp_id, c.name "
        "FROM corp_members m "
        "JOIN corps c ON c.corp_id=m.corp_id "
        "WHERE m.user_id=? "
        "ORDER BY CASE m.role "
        "           WHEN 'owner' THEN 0 "
        "           WHEN 'deputy' THEN 1 "
        "           ELSE 2 "
        "         END, m.joined_at ASC "
        "LIMIT 1",
        (int(user_id),)
    )
    if not r:
        return 0, ""

    cid = int(r["corp_id"] or 0)
    cname = (r["name"] or "").strip()

    if cid > 0:
        db_exec(
            "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
            (cid, cname, int(user_id)),
            commit=True
        )
    return cid, cname

def same_corp(viewer_id: int, target_id: int) -> bool:
    c1, _ = get_user_corp_resolved(int(viewer_id))
    c2, _ = get_user_corp_resolved(int(target_id))
    return (c1 > 0) and (c1 == c2)

def corp_by_name(name: str):
    nm = (name or "").strip()
    if not nm:
        return None
    return db_one("SELECT corp_id, name, owner_id, created_chat_id, created_at, is_open, min_bio_exp, description "
                  "FROM corps WHERE lower(name)=lower(?) LIMIT 1", (nm,))

def corp_by_id(corp_id: int):
    return db_one("SELECT corp_id, name, owner_id, created_chat_id, created_at, is_open, min_bio_exp, description "
                  "FROM corps WHERE corp_id=? LIMIT 1", (int(corp_id),))

def corp_role(corp_id: int, user_id: int) -> str:
    r = db_one("SELECT role FROM corp_members WHERE corp_id=? AND user_id=? LIMIT 1",
               (int(corp_id), int(user_id)))
    return (r["role"] or "") if r else ""

def corp_is_member(corp_id: int, user_id: int) -> bool:
    return bool(corp_role(corp_id, user_id))

def corp_is_owner_or_deputy(corp_id: int, user_id: int) -> bool:
    role = corp_role(corp_id, user_id)
    return role in ("owner", "deputy")

def corp_sums(corp_id: int) -> tuple[int, int]:
    r = db_one(
        "SELECT COALESCE(SUM(l.bio_exp),0) AS be, COALESCE(SUM(l.infected_total),0) AS inf "
        "FROM corp_members m JOIN labs l ON l.user_id=m.user_id WHERE m.corp_id=?",
        (int(corp_id),)
    )
    if not r:
        return 0, 0
    return int(r["be"] or 0), int(r["inf"] or 0)

def corp_deputies(corp_id: int):
    return db_all(
        "SELECT m.user_id, u.username, u.first_name, u.last_name "
        "FROM corp_members m LEFT JOIN users u ON u.user_id=m.user_id "
        "WHERE m.corp_id=? AND m.role='deputy' ORDER BY m.joined_at ASC",
        (int(corp_id),)
    ) or []

def corp_owner(corp_id: int):
    return db_one(
        "SELECT m.user_id, u.username, u.first_name, u.last_name "
        "FROM corp_members m LEFT JOIN users u ON u.user_id=m.user_id "
        "WHERE m.corp_id=? AND m.role='owner' LIMIT 1",
        (int(corp_id),)
    )

def corp_members_full(corp_id: int):
    return db_all(
        "SELECT m.user_id, m.role, m.joined_at, "
        "COALESCE(l.bio_exp,0) AS be, COALESCE(l.infected_total,0) AS sick, "
        "u.username, u.first_name, u.last_name "
        "FROM corp_members m "
        "LEFT JOIN labs l ON l.user_id=m.user_id "
        "LEFT JOIN users u ON u.user_id=m.user_id "
        "WHERE m.corp_id=?",
        (int(corp_id),)
    ) or []

def corp_name_display(name: str) -> str:
    nm = (name or "").strip()
    if not nm:
        return ""
    if nm.lower().startswith("им."):
        return h(nm)
    return f"«{h(nm)}»"

def _default_corp_name_for_owner(owner_id: int, exclude_corp_id: int = 0) -> str:
    owner_id = int(owner_id)
    exclude_corp_id = int(exclude_corp_id or 0)

    u = get_user_row(owner_id)
    un = (u["username"] or "") if u else ""
    disp = standard_display_name(
        (u["first_name"] or "") if u else "",
        (u["last_name"] or "") if u else "",
        un,
        owner_id
    )
    base = f"им. {disp}".strip() if disp else f"им. {owner_id}"
    if len(base) > 40:
        base = base[:40].rstrip() or f"им. {owner_id}"

    ex = corp_by_name(base)
    if not ex or int(ex["corp_id"] or 0) == exclude_corp_id:
        return base

    suffix = f" {owner_id}"
    trimmed = base[:max(1, 40 - len(suffix))].rstrip()
    cand = f"{trimmed}{suffix}".strip()
    ex = corp_by_name(cand)
    if not ex or int(ex["corp_id"] or 0) == exclude_corp_id:
        return cand

    return (f"им. {owner_id}")[:40]

def _reset_owned_corp_name_to_default(owner_id: int):
    owner_id = int(owner_id)
    cid, _ = get_user_corp_resolved(owner_id)
    if cid <= 0:
        return

    corp = corp_by_id(int(cid))
    if not corp:
        return

    if int(corp["owner_id"] or 0) != owner_id:
        return

    new_name = _default_corp_name_for_owner(owner_id, exclude_corp_id=int(cid))

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute("UPDATE corps SET name=? WHERE corp_id=?", (new_name, int(cid)))
            c.execute(
                "UPDATE labs SET corp_name=? WHERE user_id IN (SELECT user_id FROM corp_members WHERE corp_id=?)",
                (new_name, int(cid))
            )
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def corp_clickable_name(corp_row) -> str:
    nm = corp_name_display((corp_row["name"] or "").strip())
    if corp_is_open_value(corp_row) != 1:
        return nm

    owner_id = int(corp_row["owner_id"] or 0)
    if owner_id <= 0:
        return nm

    owner = get_user_row(owner_id)
    owner_un = (owner["username"] or "") if owner else ""
    return tg_mention(owner_id, nm, username=owner_un)

def corp_is_open_value(corp_row) -> int:
    try:
        v = corp_row["is_open"]
        return 1 if v is None else int(v)
    except Exception:
        return 1

def kb_corp_request_actions(request_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        InlineKeyboardButton("Принять", callback_data=f"{CB_CORP_REQ_APPROVE}:{int(request_id)}", style="success"),
        InlineKeyboardButton("Отказать", callback_data=f"{CB_CORP_REQ_REJECT}:{int(request_id)}", style="danger")
    )
    return kb

def _corp_actor_tag(user_id: int) -> str:
    row = get_user_row(int(user_id))
    if not row:
        return str(int(user_id))
    un = (row["username"] or "")
    disp = display_name(row["first_name"] or "", row["last_name"] or "", un, int(user_id))
    return tg_mention(int(user_id), disp, username=un)

def corp_manager_ids(corp_id: int) -> list[int]:
    ids: list[int] = []
    owner = corp_owner(int(corp_id))
    if owner:
        ids.append(int(owner["user_id"]))
    for d in corp_deputies(int(corp_id)):
        did = int(d["user_id"])
        if did not in ids:
            ids.append(did)
    return ids

def _corp_remove_member(corp_id: int, user_id: int):
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute("DELETE FROM corp_members WHERE corp_id=? AND user_id=?", (int(corp_id), int(user_id)))
            c.execute("UPDATE labs SET corp_id=0, corp_name='' WHERE user_id=?", (int(user_id),))
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _corp_notify_leave(corp_id: int, user_id: int):
    user_tag = _corp_actor_tag(int(user_id))
    text = f"📄 Игрок {user_tag} {_gender_pick(int(user_id), 'corp_leave_notify')}.\nКорпорация осталась без ценного кадра."

    for mid in corp_notice_manager_ids(int(corp_id)):
        if int(mid) == int(user_id):
            continue
        try:
            bot.send_message(int(mid), text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            pass

def _corp_notify_kicked(target_id: int, corp_row):
    try:
        bot.send_message(
            int(target_id),
            f"📄 {_gender_pick(int(target_id), 'corp_kick_target')} {corp_name_display(corp_row['name'])}.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    except Exception:
        pass

def _corp_pick_new_owner_target(corp_id: int, exclude_user_id: int) -> int:
    r = db_one(
        "SELECT user_id FROM corp_members "
        "WHERE corp_id=? AND user_id<>? AND role='deputy' "
        "ORDER BY joined_at ASC LIMIT 1",
        (int(corp_id), int(exclude_user_id))
    )
    if r:
        return int(r["user_id"])

    r = db_one(
        "SELECT user_id FROM corp_members "
        "WHERE corp_id=? AND user_id<>? AND role='member' "
        "ORDER BY joined_at ASC LIMIT 1",
        (int(corp_id), int(exclude_user_id))
    )
    if r:
        return int(r["user_id"])

    return 0

def _corp_transfer_owner_rights(corp_id: int, old_owner_id: int, new_owner_id: int):
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute("UPDATE corps SET owner_id=? WHERE corp_id=?", (int(new_owner_id), int(corp_id)))
            c.execute("UPDATE corp_members SET role='member' WHERE corp_id=? AND user_id=?", (int(corp_id), int(old_owner_id)))
            c.execute("UPDATE corp_members SET role='owner' WHERE corp_id=? AND user_id=?", (int(corp_id), int(new_owner_id)))
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _parse_corp_transfer_args(message, parsed: "Parsed"):
    """
    Для команд:
      передать р N @user
      передать м N @user
    Или reply на сообщение игрока:
      передать р N
      передать м N
    Возвращает: (amount, target_id, target_user_obj, token)
    """
    args = (parsed.args or "").strip()
    if not args:
        return 0, None, None, ""

    parts = args.split(None, 1)
    if not parts or not parts[0].isdigit():
        return 0, None, None, ""

    amount = int(parts[0])
    tail = parts[1].strip() if len(parts) > 1 else ""

    fake = Parsed(
        raw=parsed.raw,
        has_prefix_char=parsed.has_prefix_char,
        prefix_char=parsed.prefix_char,
        cmd=parsed.cmd,
        args=tail
    )
    target_id, target_user_obj = resolve_target_from_reply_or_args(message, fake)
    tok = (tail.split()[0] if tail else "")
    return amount, target_id, target_user_obj, tok

def _corp_transfer_shortage_error(cmd: str) -> str:
    if str(cmd or "").strip() == "corp_send_res":
        return "📝 У вас нет столько био-ресурсов."
    return "📝 У вас нет столько био-материалов."

def _corp_transfer_mode_code(cmd: str) -> str:
    return "R" if str(cmd or "").strip() == "corp_send_res" else "M"

def _corp_transfer_cmd_from_mode(mode: str) -> str:
    m = str(mode or "").strip().upper()
    if m == "R":
        return "corp_send_res"
    if m == "M":
        return "corp_send_mat"
    return ""

def _corp_transfer_plan(sender_id: int, cmd: str, amount: int) -> dict:
    amount = max(1, int(amount or 0))
    cmd = str(cmd or "").strip()

    row = db_one(
        "SELECT COALESCE(all_bio_res,0) AS ar, COALESCE(all_bio_mater,0) AS am "
        "FROM labs WHERE user_id=?",
        (int(sender_id),)
    )
    have_r = int(row["ar"] or 0) if row else 0
    have_m = int(row["am"] or 0) if row else 0

    plan = {
        "ok": False,
        "pure": False,
        "mixed": False,
        "substitute_only": False,
        "cmd": cmd,
        "amount": amount,
        "have_r": have_r,
        "have_m": have_m,
        "res_amount": 0,
        "mat_amount": 0,
        "requested_currency": "res" if cmd == "corp_send_res" else "mat",
        "actual_currency": "",
    }

    if cmd == "corp_send_res":
        if have_r >= amount:
            plan["ok"] = True
            plan["pure"] = True
            plan["res_amount"] = int(amount)
            plan["actual_currency"] = "res"
            return plan

        if have_m >= amount and have_r <= 0:
            plan["ok"] = True
            plan["substitute_only"] = True
            plan["mat_amount"] = int(amount)
            plan["actual_currency"] = "mat"
            return plan

        if (have_r + have_m) >= amount:
            plan["ok"] = True
            plan["mixed"] = True
            plan["res_amount"] = int(max(0, have_r))
            plan["mat_amount"] = int(amount - plan["res_amount"])
            plan["actual_currency"] = "mixed"
            return plan

        return plan

    if cmd == "corp_send_mat":
        if have_m >= amount:
            plan["ok"] = True
            plan["pure"] = True
            plan["mat_amount"] = int(amount)
            plan["actual_currency"] = "mat"
            return plan

        if have_r >= amount and have_m <= 0:
            plan["ok"] = True
            plan["substitute_only"] = True
            plan["res_amount"] = int(amount)
            plan["actual_currency"] = "res"
            return plan

        if (have_r + have_m) >= amount:
            plan["ok"] = True
            plan["mixed"] = True
            plan["mat_amount"] = int(max(0, have_m))
            plan["res_amount"] = int(amount - plan["mat_amount"])
            plan["actual_currency"] = "mixed"
            return plan

        return plan

    return plan

def _corp_transfer_mix_text(cmd: str, target_id: int, res_amount: int, mat_amount: int) -> str:
    shortage = _corp_transfer_shortage_error(cmd)
    target_tag = _corp_actor_tag(int(target_id))

    res_amount = int(res_amount or 0)
    mat_amount = int(mat_amount or 0)

    if res_amount <= 0 and mat_amount > 0:
        return (
            f"{shortage}\n"
            f"Однако для перевода игроку <b>{target_tag}</b> можно полностью заменить сумму на био-материалы:\n"
            f"💊 {_fmt_k(mat_amount)}\n"
            "Подтвердить перевод?"
        )

    if mat_amount <= 0 and res_amount > 0:
        return (
            f"{shortage}\n"
            f"Однако для перевода игроку <b>{target_tag}</b> можно полностью заменить сумму на био-ресурсы:\n"
            f"🧬 {_fmt_k(res_amount)}\n"
            "Подтвердить перевод?"
        )

    return (
        f"{shortage}\n"
        f"Однако для перевода игроку <b>{target_tag}</b> можно использовать смешанную сумму:\n"
        f"🧬 {_fmt_k(res_amount)} + 💊 {_fmt_k(mat_amount)}\n"
        "Подтвердить перевод?"
    )

def _corp_transfer_success_text(target_id: int, res_amount: int, mat_amount: int) -> str:
    target_tag = _corp_actor_tag(int(target_id))
    res_amount = int(res_amount or 0)
    mat_amount = int(mat_amount or 0)

    if res_amount > 0 and mat_amount > 0:
        return (
            f"✅Успех. Игроку <b>{target_tag}</b> передано "
            f"🧬 {_fmt_k(res_amount)} + 💊 {_fmt_k(mat_amount)}."
        )

    if res_amount > 0:
        word = _ru_form(int(res_amount), "био-ресурс", "био-ресурса", "био-ресурсов")
        return f"✅Успех. Игроку <b>{target_tag}</b> передано 🧬 {_fmt_k(int(res_amount))} {word}."

    word = _ru_form(int(mat_amount), "био-материал", "био-материала", "био-материалов")
    return f"✅Успех. Игроку <b>{target_tag}</b> передано 💊 {_fmt_k(int(mat_amount))} {word}."

def _corp_transfer_notify_text(sender_id: int, res_amount: int, mat_amount: int) -> str:
    sender_tag = _corp_actor_tag(int(sender_id))
    res_amount = int(res_amount or 0)
    mat_amount = int(mat_amount or 0)

    if res_amount > 0 and mat_amount > 0:
        return (
            f"🏦 Участник вашей Корпорации <b>{sender_tag}</b> перевёл вам "
            f"🧬 {_fmt_k(res_amount)} + 💊 {_fmt_k(mat_amount)}."
        )

    if res_amount > 0:
        word = _ru_form(int(res_amount), "био-ресурс", "био-ресурса", "био-ресурсов")
        return (
            f"🏦 Участник вашей Корпорации <b>{sender_tag}</b> перевёл вам "
            f"🧬 {_fmt_k(int(res_amount))} {word}."
        )

    word = _ru_form(int(mat_amount), "био-материал", "био-материала", "био-материалов")
    return (
        f"🏦 Участник вашей Корпорации <b>{sender_tag}</b> перевёл вам "
        f"💊 {_fmt_k(int(mat_amount))} {word}."
    )

def _maybe_send_corp_transfer_notification(sender_id: int, target_id: int, res_amount: int, mat_amount: int):
    try:
        sender_id = int(sender_id)
        target_id = int(target_id)
        res_amount = int(res_amount or 0)
        mat_amount = int(mat_amount or 0)

        if target_id <= 0 or sender_id <= 0 or sender_id == target_id:
            return

        if res_amount <= 0 and mat_amount <= 0:
            return

        if corp_notify_enabled(int(target_id)) != 1:
            return

        send_user_notification(
            int(target_id),
            _corp_transfer_notify_text(int(sender_id), int(res_amount), int(mat_amount)),
            respect_notify_off=False
        )

    except Exception as e:
        send_error_report("corp_transfer_notify", e)

def _corp_transfer_mix_cb(action: str, uid: int, cmd: str, target_id: int, res_amount: int, mat_amount: int) -> str:
    return (
        f"{CB_CORP_TX}:{str(action or '').strip().upper()}:{int(uid)}:"
        f"{_corp_transfer_mode_code(cmd)}:{int(target_id)}:{int(res_amount)}:{int(mat_amount)}"
    )

def kb_corp_transfer_mix_offer(uid: int, cmd: str, target_id: int, res_amount: int, mat_amount: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        InlineKeyboardButton(
            "Согласиться",
            callback_data=_corp_transfer_mix_cb("A", int(uid), cmd, int(target_id), int(res_amount), int(mat_amount)),
            style="success"
        ),
        InlineKeyboardButton(
            "Прервать перевод",
            callback_data=_corp_transfer_mix_cb("C", int(uid), cmd, int(target_id), int(res_amount), int(mat_amount)),
            style="danger"
        )
    )
    return kb

def _corp_transfer_apply(sender_id: int, target_id: int, *, res_amount: int = 0, mat_amount: int = 0) -> tuple[bool, str]:
    res_amount = int(res_amount or 0)
    mat_amount = int(mat_amount or 0)

    if res_amount < 0 or mat_amount < 0 or (res_amount == 0 and mat_amount == 0):
        return False, "📑 Некорректная сумма перевода."

    s = db_one(
        "SELECT COALESCE(all_bio_res,0) AS ar, COALESCE(all_bio_mater,0) AS am "
        "FROM labs WHERE user_id=?",
        (int(sender_id),)
    )
    t = db_one(
        "SELECT COALESCE(all_bio_res,0) AS ar, COALESCE(all_bio_mater,0) AS am "
        "FROM labs WHERE user_id=?",
        (int(target_id),)
    )

    if not s or not t:
        return False, "📑 Не удалось выполнить перевод."

    s_ar = int(s["ar"] or 0)
    s_am = int(s["am"] or 0)
    t_ar = int(t["ar"] or 0)
    t_am = int(t["am"] or 0)

    if s_ar < res_amount:
        return False, "📝 У вас нет столько био-ресурсов."
    if s_am < mat_amount:
        return False, "📝 У вас нет столько био-материалов."

    new_s_ar = s_ar - res_amount
    new_s_am = s_am - mat_amount
    new_t_ar = t_ar + res_amount
    new_t_am = t_am + mat_amount

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            c.execute(
                "UPDATE labs SET all_bio_res=?, all_bio_mater=?, bio_res=? WHERE user_id=?",
                (int(new_s_ar), int(new_s_am), int(new_s_ar), int(sender_id))
            )
            c.execute(
                "UPDATE labs SET all_bio_res=?, all_bio_mater=?, bio_res=? WHERE user_id=?",
                (int(new_t_ar), int(new_t_am), int(new_t_ar), int(target_id))
            )

            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    _maybe_send_corp_transfer_notification(
        int(sender_id),
        int(target_id),
        int(res_amount),
        int(mat_amount)
    )

    return True, ""

def _extract_single_corp_name_from_text(text: str) -> str:
    s = (text or "").strip()
    if not s:
        return ""

    found = []
    for m in re.finditer(r"Досье\s+Корпорации\s+«([^»]+)»", s, flags=re.IGNORECASE):
        nm = (m.group(1) or "").strip()
        if nm:
            found.append(nm)
    for m in re.finditer(r"Досье\s+корпорации\s+«([^»]+)»", s, flags=re.IGNORECASE):
        nm = (m.group(1) or "").strip()
        if nm:
            found.append(nm)
    for m in re.finditer(r"Досье\s+Корпорации\s+(им\.[^\n<]+)", s, flags=re.IGNORECASE):
        nm = (m.group(1) or "").strip()
        if nm:
            found.append(nm)
    for m in re.finditer(r"Досье\s+корпорации\s+(им\.[^\n<]+)", s, flags=re.IGNORECASE):
        nm = (m.group(1) or "").strip()
        if nm:
            found.append(nm)

    uniq = []
    seen = set()
    for nm in found:
        key = nm.casefold()
        if key not in seen:
            seen.add(key)
            uniq.append(nm)
    return uniq[0] if len(uniq) == 1 else ""

def resolve_corp_for_join(message, parsed: "Parsed"):
    name = (parsed.args or "").strip()
    if name:
        corp = corp_by_name(name)
        if corp:
            return corp

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        if target_id is not None:
            if target_user_obj is not None:
                capture_user_context(message, target_user_obj)

            rcid, _ = get_user_corp_resolved(int(target_id))
            if rcid > 0:
                corp = corp_by_id(int(rcid))
                if corp:
                    return corp

        return None

    target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
    if target_id is not None:
        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        rcid, _ = get_user_corp_resolved(int(target_id))
        if rcid > 0:
            corp = corp_by_id(int(rcid))
            if corp:
                return corp

    if message.reply_to_message:
        txt = (getattr(message.reply_to_message, "text", "") or getattr(message.reply_to_message, "caption", "") or "")
        nm = _extract_single_corp_name_from_text(txt)
        if nm:
            return corp_by_name(nm)

    return None

def _corp_join_open(user_id: int, corp_row) -> bool:
    corp_id = int(corp_row["corp_id"])
    name = (corp_row["name"] or "").strip()
    now = now_ts()

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT OR REPLACE INTO corp_members(corp_id, user_id, role, joined_at) VALUES (?,?, 'member', ?)",
                (corp_id, int(user_id), now)
            )
            c.execute(
                "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                (corp_id, name, int(user_id))
            )
            conn.commit()
            return True
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _send_corp_join_notices(corp_row, joined_user_id: int):
    corp_id = int(corp_row["corp_id"])
    joined_tag = _corp_actor_tag(int(joined_user_id))
    text = f"📑 Игрок {joined_tag} {_gender_pick(int(joined_user_id), 'corp_invite_accept')}."

    for mid in corp_notice_manager_ids(corp_id):
        if int(mid) == int(joined_user_id):
            continue
        try:
            bot.send_message(int(mid), text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            pass

def _create_corp_request(
    corp_row,
    requester_id: int,
    *,
    user_chat_id: int,
    user_reply_to: int = 0,
    send_user_notice: bool = True
) -> int:
    corp_id = int(corp_row["corp_id"])
    now = now_ts()
    expires_at = int(now + 86400)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT INTO corp_requests(corp_id, user_id, created_at, expires_at, status) VALUES (?,?,?,?, 'pending')",
                (corp_id, int(requester_id), now, expires_at)
            )
            request_id = int(c.lastrowid)
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    user_tag = _corp_actor_tag(int(requester_id))
    owner_text = (
        f"📄 Заявка на вступление от {user_tag}\n"
        f"ID заявки: <code>{request_id}</code>\n"
        "Решение за вами:"
    )

    for mid in corp_manager_ids(corp_id):
        try:
            sent = bot.send_message(
                int(mid),
                owner_text,
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=kb_corp_request_actions(request_id)
            )
            db_exec(
                "INSERT OR IGNORE INTO corp_request_msgs(request_id, chat_id, msg_id, kind) VALUES (?,?,?,?)",
                (request_id, int(sent.chat.id), int(sent.message_id), "owner" if int(mid) == int(corp_row["owner_id"]) else "deputy"),
                commit=True
            )
        except Exception:
            pass

    user_text = f"📄 Ваша заявка на вступление в Корпорацию {corp_name_display(corp_row['name'])} отправлена."
    if send_user_notice:
        try:
            sent = bot.send_message(
                int(user_chat_id),
                user_text,
                reply_to_message_id=int(user_reply_to) if int(user_reply_to or 0) > 0 else None,
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            db_exec(
                "INSERT OR IGNORE INTO corp_request_msgs(request_id, chat_id, msg_id, kind) VALUES (?,?,?, 'user')",
                (request_id, int(sent.chat.id), int(sent.message_id)),
                commit=True
            )
        except Exception:
            pass

    return request_id

def corp_request_by_id(request_id: int):
    return db_one(
        "SELECT request_id, corp_id, user_id, created_at, expires_at, status "
        "FROM corp_requests WHERE request_id=? LIMIT 1",
        (int(request_id),)
    )

def _extract_request_id_from_text(text: str) -> int:
    s = (text or "").strip()
    if not s:
        return 0
    m = re.search(r"ID\s+заявки:\s*(\d+)", s, flags=re.IGNORECASE)
    if m:
        return int(m.group(1))
    return 0

def _resolve_request_id_from_message_or_args(message, parsed: "Parsed") -> int:
    args = (parsed.args or "").strip()
    if args.isdigit():
        return int(args)

    if message.reply_to_message:
        txt = (
            getattr(message.reply_to_message, "text", "") or
            getattr(message.reply_to_message, "caption", "") or
            ""
        )
        rid = _extract_request_id_from_text(txt)
        if rid > 0:
            return rid

    return 0

def _corp_request_actor_role_word(corp_id: int, actor_id: int) -> str:
    role = corp_role(int(corp_id), int(actor_id))
    if role == "owner":
        return _gender_pick(int(actor_id), "corp_request_actor_owner_ins")
    if role == "deputy":
        return _gender_pick(int(actor_id), "corp_request_actor_deputy_ins")
    return _gender_pick(int(actor_id), "corp_request_actor_member_ins")

def _corp_request_texts(req_row, actor_id: int, approved: bool) -> tuple[str, str]:
    user_id = int(req_row["user_id"])
    user_tag = _corp_actor_tag(user_id)

    if approved:
        manager_text = f"📑 Игрок {user_tag} {_gender_pick(user_id, 'corp_invite_accept')}"
        user_text = "✅ Вы приняты в Корпорацию."
        return manager_text, user_text

    actor_tag = _corp_actor_tag(int(actor_id))
    who = _corp_request_actor_role_word(int(req_row["corp_id"]), int(actor_id))
    manager_text = f"📄 Заявка игрока {user_tag} была отклонена {who} {actor_tag}"
    user_text = "❌ Ваша заявка была отклонена"
    return manager_text, user_text

def _corp_request_edit_all(request_id: int, manager_text: str, user_text: str):
    rows = db_all(
        "SELECT chat_id, msg_id, kind FROM corp_request_msgs WHERE request_id=? ORDER BY kind ASC, chat_id ASC, msg_id ASC",
        (int(request_id),)
    ) or []

    for r in rows:
        kind = (r["kind"] or "").strip().lower()
        text = user_text if kind == "user" else manager_text

        try:
            limited_edit_message_text(
                text=text,
                chat_id=int(r["chat_id"]),
                msg_id=int(r["msg_id"]),
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        except Exception:
            pass

def _corp_request_resolve(request_id: int, actor_id: int, approved: bool) -> tuple[bool, str]:
    req = corp_request_by_id(int(request_id))
    if not req:
        return False, "📑 Заявка не найдена."

    if (req["status"] or "") != "pending":
        if (req["status"] or "").strip() == "expired":
            return False, "📑 Срок рассмотрения этой заявки уже истёк."
        return False, "📑 Эта заявка уже рассмотрена."

    corp_id = int(req["corp_id"])
    user_id = int(req["user_id"])

    if not corp_is_owner_or_deputy(corp_id, int(actor_id)):
        return False, "📑 Решение по заявке могут принимать только агенты тех.поддержки."

    corp = corp_by_id(corp_id)
    if not corp:
        return False, "📑 Корпорация не найдена."

    if approved:
        if not is_lab_active(user_id):
            return False, "📑 Игрок ещё не создал свою лабораторию."

        user_cid, _ = get_user_corp_resolved(user_id)
        if user_cid > 0:
            return False, "📑 Игрок уже состоит в Корпорации."

        now = now_ts()
        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")
                c.execute("UPDATE corp_requests SET status='approved' WHERE request_id=?", (int(request_id),))
                c.execute(
                    "INSERT INTO corp_members(corp_id, user_id, role, joined_at) VALUES (?,?, 'member', ?)",
                    (corp_id, user_id, now)
                )
                c.execute(
                    "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                    (corp_id, (corp["name"] or "").strip(), user_id)
                )
                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        manager_text, user_text = _corp_request_texts(req, actor_id, True)
        _corp_request_edit_all(int(request_id), manager_text, user_text)
        return True, "✅ Заявка принята."

    db_exec("UPDATE corp_requests SET status='rejected' WHERE request_id=?", (int(request_id),), commit=True)
    manager_text, user_text = _corp_request_texts(req, actor_id, False)
    _corp_request_edit_all(int(request_id), manager_text, user_text)
    return True, "❎ Заявка отклонена."

def _corp_request_expired_texts(req_row) -> tuple[str, str]:
    corp = corp_by_id(int(req_row["corp_id"]))
    corp_txt = corp_name_display(corp["name"]) if corp else "Корпорацию"
    user_tag = _corp_actor_tag(int(req_row["user_id"]))

    manager_text = f"⌛ Срок рассмотрения заявки игрока {user_tag} на вступление в {corp_txt} истёк."
    user_text = f"⌛ Срок рассмотрения вашей заявки на вступление в {corp_txt} истёк."
    return manager_text, user_text

def _corp_request_expire(request_id: int):
    req = corp_request_by_id(int(request_id))
    if not req:
        return
    if (req["status"] or "").strip() != "pending":
        return

    rc = db_exec(
        "UPDATE corp_requests SET status='expired' WHERE request_id=? AND status='pending'",
        (int(request_id),),
        commit=True
    )
    if int(rc or 0) <= 0:
        return

    manager_text, user_text = _corp_request_expired_texts(req)
    _corp_request_edit_all(int(request_id), manager_text, user_text)

def _corp_invite_expired_text(inv_row) -> str:
    corp = corp_by_id(int(inv_row["corp_id"]))
    corp_txt = corp_name_display(corp["name"]) if corp else "Корпорацию"
    invited_tag = _corp_actor_tag(int(inv_row["user_id"]))
    return f"⌛ Срок действия приглашения игрока {invited_tag} в {corp_txt} истёк."

def _corp_invite_expire(invite_id: int):
    inv = corp_invite_by_id(int(invite_id))
    if not inv:
        return
    if (inv["status"] or "").strip() != "pending":
        return

    rc = db_exec(
        "UPDATE corp_invites SET status='expired' WHERE invite_id=? AND status='pending'",
        (int(invite_id),),
        commit=True
    )
    if int(rc or 0) <= 0:
        return

    text = _corp_invite_expired_text(inv)
    try:
        limited_edit_message_text(
            text=text,
            chat_id=int(inv["chat_id"]),
            msg_id=int(inv["msg_id"]),
            parse_mode="HTML",
            reply_markup=None,
            disable_web_page_preview=True
        )
    except Exception:
        pass

def kb_corp_invite_actions(invite_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        InlineKeyboardButton("Вступить", callback_data=f"{CB_CORP_INV_ACCEPT}:{int(invite_id)}", style="success"),
        InlineKeyboardButton("Отказать", callback_data=f"{CB_CORP_INV_REJECT}:{int(invite_id)}", style="danger")
    )
    return kb

def corp_invite_by_id(invite_id: int):
    return db_one(
        "SELECT invite_id, corp_id, user_id, invited_by, created_at, expires_at, status, chat_id, msg_id "
        "FROM corp_invites WHERE invite_id=? LIMIT 1",
        (int(invite_id),)
    )

def _corp_inviter_prefix(corp_id: int, inviter_id: int) -> str:
    role = corp_role(int(corp_id), int(inviter_id))
    if role == "owner":
        return _gender_pick(int(inviter_id), "corp_inviter_role_owner")
    if role == "deputy":
        return _gender_pick(int(inviter_id), "corp_inviter_role_deputy")
    return ""

def _corp_invite_chat_text(corp_row, invited_id: int, inviter_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    inviter_tag = _corp_actor_tag(int(inviter_id))
    prefix = _corp_inviter_prefix(int(corp_row["corp_id"]), int(inviter_id))
    return (
        f"✉️ {invited_tag}, минуточку внимания. "
        f"{prefix}{inviter_tag} {_gender_pick(int(inviter_id), 'corp_invite_chat')} {corp_name_display(corp_row['name'])}"
    )

def _corp_invite_accept_text(corp_row, invited_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    return (
        f"✅ Игрок {invited_tag} {_gender_pick(int(invited_id), 'corp_invite_accept')} {corp_name_display(corp_row['name'])}.\n"
        "Встречайте новичка."
    )

def _corp_invite_reject_text(corp_row, invited_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    return (
        f"❌ Игрок {invited_tag} {_gender_pick(int(invited_id), 'corp_invite_reject')} {corp_name_display(corp_row['name'])}."
    )

def _corp_invite_notify_accept(corp_row, inviter_id: int, invited_id: int):
    corp_id = int(corp_row["corp_id"])
    inviter_tag = _corp_actor_tag(int(inviter_id))
    invited_tag = _corp_actor_tag(int(invited_id))
    prefix = _corp_inviter_prefix(corp_id, int(inviter_id))
    text = (
        f"📄 {prefix}{inviter_tag} {_gender_pick(int(inviter_id), 'corp_invite_notify_accept')} {invited_tag} "
        f"в Корпорацию {corp_name_display(corp_row['name'])}."
    )

    for mid in corp_notice_manager_ids(corp_id):
        try:
            bot.send_message(int(mid), text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            pass

def _create_corp_invite(corp_row, invited_id: int, invited_by: int, *, chat_id: int) -> int:
    corp_id = int(corp_row["corp_id"])
    now = now_ts()
    expires_at = int(now + 86400)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT INTO corp_invites(corp_id, user_id, invited_by, created_at, expires_at, status, chat_id, msg_id) "
                "VALUES (?,?,?,?,?,'pending',?,0)",
                (corp_id, int(invited_id), int(invited_by), now, expires_at, int(chat_id))
            )
            invite_id = int(c.lastrowid)
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    text = _corp_invite_chat_text(corp_row, int(invited_id), int(invited_by))
    sent = bot.send_message(
        int(chat_id),
        text,
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_corp_invite_actions(invite_id)
    )

    db_exec(
        "UPDATE corp_invites SET msg_id=? WHERE invite_id=?",
        (int(sent.message_id), int(invite_id)),
        commit=True
    )
    return invite_id

def _corp_invite_resolve(invite_id: int, actor_id: int, accepted: bool) -> tuple[bool, str]:
    inv = corp_invite_by_id(int(invite_id))
    if not inv:
        return False, "📑 Приглашение не найдено."

    status = (inv["status"] or "").strip()
    if status != "pending":
        if status == "expired":
            return False, "📑 Срок действия этого приглашения уже истёк."
        return False, "📑 Это приглашение уже обработано."

    if int(inv["user_id"]) != int(actor_id):
        return False, "📑 Это приглашение адресовано не вам."

    corp = corp_by_id(int(inv["corp_id"]))
    if not corp:
        return False, "📑 Корпорация не найдена."

    user_id = int(inv["user_id"])
    inviter_id = int(inv["invited_by"])

    if accepted:
        if not is_lab_active(user_id):
            return False, "📑 Сначала создайте лабораторию."

        user_cid, _ = get_user_corp_resolved(user_id)
        if user_cid > 0:
            return False, "📑 Вы уже состоите в Корпорации."

        min_be = int(corp["min_bio_exp"] or 0)
        my_lab = get_lab(user_id)
        my_be = int(my_lab["bio_exp"] or 0)
        if min_be > 0 and my_be < min_be:
            return False, "📝 Вашего био-опыта недостаточно для вступления."

        now = now_ts()
        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")
                c.execute("UPDATE corp_invites SET status='accepted' WHERE invite_id=?", (int(invite_id),))
                c.execute(
                    "INSERT INTO corp_members(corp_id, user_id, role, joined_at) VALUES (?,?, 'member', ?)",
                    (int(corp["corp_id"]), user_id, now)
                )
                c.execute(
                    "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                    (int(corp["corp_id"]), (corp["name"] or "").strip(), user_id)
                )
                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        text = _corp_invite_accept_text(corp, user_id)
        try:
            limited_edit_message_text(
                text=text,
                chat_id=int(inv["chat_id"]),
                msg_id=int(inv["msg_id"]),
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        except Exception:
            pass

        _corp_invite_notify_accept(corp, inviter_id, user_id)
        return True, f"✅ Вы вступили в Корпорацию."

    db_exec("UPDATE corp_invites SET status='declined' WHERE invite_id=?", (int(invite_id),), commit=True)
    text = _corp_invite_reject_text(corp, user_id)
    try:
        limited_edit_message_text(
            text=text,
            chat_id=int(inv["chat_id"]),
            msg_id=int(inv["msg_id"]),
            parse_mode="HTML",
            reply_markup=None,
            disable_web_page_preview=True
        )
    except Exception:
        pass

    return True, "🗑️ Приглашение отклонено."

def kb_corp_info(corp_id: int, viewer_id: int, is_member: bool) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)

    if is_member:
        kb.add(InlineKeyboardButton("Участники", callback_data=f"{CORPUI_TAG}:M:{int(corp_id)}:{int(viewer_id)}", style="primary"))

        role = corp_role(int(corp_id), int(viewer_id))
        corp = corp_by_id(int(corp_id))
        if corp and role in ("owner", "deputy"):
            req_row = db_one(
                "SELECT COUNT(*) AS c FROM corp_requests WHERE corp_id=? AND status='pending'",
                (int(corp_id),)
            )
            req_count = int(req_row["c"] or 0) if req_row else 0

            type_btn = (
                InlineKeyboardButton("Закрыть корпу", callback_data=f"{CORPUI_TAG}:C:{int(corp_id)}:{int(viewer_id)}", style="danger")
                if corp_is_open_value(corp) == 1 else
                InlineKeyboardButton("Открыть корпу", callback_data=f"{CORPUI_TAG}:O:{int(corp_id)}:{int(viewer_id)}", style="success")
            )

            if req_count > 0:
                kb.row(
                    InlineKeyboardButton("Заявки", callback_data=f"{CORPUI_TAG}:R:{int(corp_id)}:{int(viewer_id)}", style="primary"),
                    type_btn
                )
            else:
                kb.add(type_btn)
    else:
        kb.add(InlineKeyboardButton("Вступить", callback_data=f"{CB_CORP_JOIN}:{int(corp_id)}:{int(viewer_id)}", style="primary"))

    return kb

def kb_corp_members(corp_id: int, viewer_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Досье Корпорации", callback_data=f"{CORPUI_TAG}:I:{int(corp_id)}:{int(viewer_id)}", style="primary"))
    return kb

def render_corp_info_text(corp_row, viewer_id: int) -> tuple[str, InlineKeyboardMarkup]:
    corp_id = int(corp_row["corp_id"])
    name = (corp_row["name"] or "").strip()
    is_open = corp_is_open_value(corp_row)
    min_be = int(corp_row["min_bio_exp"] or 0)

    owner = corp_owner(corp_id)
    deputies = corp_deputies(corp_id)
    members = corp_members_full(corp_id)
    sum_be, sum_inf = corp_sums(corp_id)

    stats_by_uid = {int(m["user_id"]): m for m in members}

    def _stats_suffix(uid: int) -> str:
        row = stats_by_uid.get(int(uid))
        if not row:
            return "☣️0|🤧0"
        return f"☣️{_fmt_k(int(row['be'] or 0))}|🤧{_fmt_k(int(row['sick'] or 0))}"

    if owner:
        ou = (owner["username"] or "")
        od = display_name(owner["first_name"] or "", owner["last_name"] or "", ou, int(owner["user_id"]))
        owner_tag = tg_mention(int(owner["user_id"]), od, username=ou)
        owner_line = f"🧑‍✈️ {_gender_pick(int(owner['user_id']), 'corp_role_owner_title')}: {owner_tag} | {_stats_suffix(int(owner['user_id']))}"
    else:
        owner_line = "🧑‍✈️ Владелец: неизвестно"

    dep_tags = []
    for d in deputies:
        du = (d["username"] or "")
        dd = display_name(d["first_name"] or "", d["last_name"] or "", du, int(d["user_id"]))
        tag = tg_mention(int(d["user_id"]), dd, username=du)
        dep_tags.append(f"{tag} | {_stats_suffix(int(d['user_id']))}")

    lines = []
    lines.append(f"🏢 Досье корпорации {corp_name_display(name)}")
    lines.append(owner_line)
    if dep_tags:
        if len(dep_tags) == 1:
            dep = deputies[0]
            lines.append(f"🧑‍💼 {_gender_pick(int(dep['user_id']), 'corp_role_deputy_title')}: {dep_tags[0]}")
        else:
            lines.append("🧑‍💼 Заместители:")
            for dline in dep_tags:
                lines.append(dline)
    lines.append("")
    lines.append(f"🏷️ Тип корпорации: {'Открытый' if is_open == 1 else 'Закрытый'}")
    if min_be > 0:
        lines.append(f"Порог вступления: {_fmt_k(min_be)}")
    lines.append("")
    lines.append(f"☣️ Био-опыт: {_fmt_k(sum_be)}")
    lines.append(f"🤧 Заражённых: {_fmt_k(sum_inf)}")
    lines.append(f"🔬 Лабораторий: {len(members)}")

    is_member = corp_is_member(corp_id, int(viewer_id))
    kb = kb_corp_info(corp_id, int(viewer_id), is_member)
    return "\n".join(lines), kb

def render_corp_members_text(corp_row, viewer_id: int) -> tuple[str, InlineKeyboardMarkup]:
    corp_id = int(corp_row["corp_id"])
    name = (corp_row["name"] or "").strip()
    members = corp_members_full(corp_id)

    owner = [m for m in members if (m["role"] or "") == "owner"]
    deps = [m for m in members if (m["role"] or "") == "deputy"]
    rest = [m for m in members if (m["role"] or "") not in ("owner", "deputy")]
    rest.sort(key=lambda r: (-int(r["be"] or 0), -int(r["sick"] or 0)))

    ordered = owner + deps + rest

    lines = []
    lines.append(f"📑СПИСОК УЧАСТНИКОВ КОРПОРАЦИИ {corp_name_display(name)}")
    lines.append("")
    i = 0
    for r in ordered:
        i += 1
        uid = int(r["user_id"])
        un = (r["username"] or "")
        disp = display_name(r["first_name"] or "", r["last_name"] or "", un, uid)
        tag = tg_mention(uid, disp, username=un)

        role = (r["role"] or "")
        pref = ""
        if role == "owner":
            pref = "💎| "
        elif role == "deputy":
            pref = "🪬| "

        be = int(r["be"] or 0)
        sick = int(r["sick"] or 0)
        lines.append(f"{i}. {pref}{tag} | ☣️ {_fmt_k(be)} | 🤧 {_fmt_k(sick)}")

        if i >= 60:
            break

    kb = kb_corp_members(corp_id, int(viewer_id))
    return "\n".join(lines), kb

def render_corp_requests_text(corp_row, viewer_id: int) -> tuple[str, InlineKeyboardMarkup]:
    corp_id = int(corp_row["corp_id"])
    name = (corp_row["name"] or "").strip()

    rows = db_all(
        "SELECT r.request_id, r.user_id, "
        "COALESCE(l.bio_exp,0) AS be, COALESCE(l.infected_total,0) AS sick, "
        "u.username, u.first_name, u.last_name "
        "FROM corp_requests r "
        "LEFT JOIN labs l ON l.user_id=r.user_id "
        "LEFT JOIN users u ON u.user_id=r.user_id "
        "WHERE r.corp_id=? AND r.status='pending' "
        "ORDER BY r.request_id ASC",
        (corp_id,)
    ) or []

    lines = []
    lines.append(f"📑 ЗАЯВКИ В КОРПОРАЦИЮ {corp_name_display(name)}")
    lines.append("")

    if not rows:
        lines.append("Активных заявок нет.")
    else:
        i = 0
        for r in rows:
            i += 1
            uid = int(r["user_id"])
            un = (r["username"] or "")
            disp = display_name(r["first_name"] or "", r["last_name"] or "", un, uid)
            tag = tg_mention(uid, disp, username=un)
            lines.append(
                f"{i}. {tag} | ☣️ {_fmt_k(int(r['be'] or 0))} | 🤧 {_fmt_k(int(r['sick'] or 0))} | ID {int(r['request_id'])}"
            )
            if i >= 60:
                break

    kb = kb_corp_members(corp_id, int(viewer_id))
    return "\n".join(lines), kb

def _top_limit_from_args(args: str) -> int:
    s = (args or "").strip()
    if not s:
        return 30
    tok = s.split()[0]
    if not tok.isdigit():
        return 30
    n = int(tok)
    if n < 1:
        n = 1
    if n > 100:
        n = 100
    return n

def _topui_data(kind: str, chat_id: int, limit: int) -> str:
    return f"{TOPUI_TAG}:{kind}:{int(chat_id)}:{int(limit)}"

def _topui_parse(data: str):
    try:
        p = (data or "").split(":")
        if len(p) != 4 or p[0] != TOPUI_TAG:
            return None
        return {
            "kind": (p[1] or "").strip().upper(),
            "chat_id": int(p[2]),
            "limit": int(p[3]),
        }
    except Exception:
        return None

def kb_top_switch(kind: str, chat_id: int, limit: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=3)
    kb.row(
        _ikb("Опыт", callback_data=_topui_data("U", int(chat_id), int(limit)), style="primary"),
        _ikb("Болезни", callback_data=_topui_data("D", int(chat_id), int(limit)), style="success"),
        _ikb("Корпорации", callback_data=_topui_data("C", int(chat_id), int(limit)), style=("primary" if (kind or "") == "C" else None)),
    )
    return kb

def _top_user_rows(limit: int):
    return db_all(
        "SELECT l.user_id, COALESCE(l.bio_exp,0) AS be, COALESCE(l.infected_total,0) AS sick, "
        "u.username, u.first_name, u.last_name "
        "FROM labs l "
        "LEFT JOIN users u ON u.user_id=l.user_id "
        "WHERE COALESCE(l.lab_active,0)=1 "
        "ORDER BY be DESC, sick DESC, l.user_id ASC "
        "LIMIT ?",
        (int(limit),)
    ) or []

def _top_user_rows_chat(chat_id: int, limit: int):
    return db_all(
        "SELECT l.user_id, COALESCE(l.bio_exp,0) AS be, COALESCE(l.infected_total,0) AS sick, "
        "u.username, u.first_name, u.last_name "
        "FROM chat_members cm "
        "JOIN labs l ON l.user_id=cm.user_id "
        "LEFT JOIN users u ON u.user_id=l.user_id "
        "WHERE cm.chat_id=? AND COALESCE(l.lab_active,0)=1 "
        "ORDER BY be DESC, sick DESC, l.user_id ASC "
        "LIMIT ?",
        (int(chat_id), int(limit))
    ) or []

def _top_disease_rows(limit: int):
    return db_all(
        "SELECT "
        "l.user_id, "
        "COALESCE(l.infected_total,0) AS sick, "
        "COALESCE(l.pathogen_name,'') AS pname, "
        "u.username, u.first_name, u.last_name "
        "FROM labs l "
        "LEFT JOIN users u ON u.user_id=l.user_id "
        "WHERE COALESCE(l.lab_active,0)=1 "
        "AND COALESCE(l.infected_total,0) > 0 "
        "ORDER BY sick DESC, l.user_id ASC "
        "LIMIT ?",
        (int(limit),)
    ) or []

def _top_disease_rows_chat(chat_id: int, limit: int):
    return db_all(
        "SELECT "
        "l.user_id, "
        "COALESCE(l.infected_total,0) AS sick, "
        "COALESCE(l.pathogen_name,'') AS pname, "
        "u.username, u.first_name, u.last_name "
        "FROM chat_members cm "
        "JOIN labs l ON l.user_id=cm.user_id "
        "LEFT JOIN users u ON u.user_id=l.user_id "
        "WHERE cm.chat_id=? "
        "AND COALESCE(l.lab_active,0)=1 "
        "AND COALESCE(l.infected_total,0) > 0 "
        "ORDER BY sick DESC, l.user_id ASC "
        "LIMIT ?",
        (int(chat_id), int(limit))
    ) or []

def _top_corp_rows(limit: int):
    return db_all(
        "SELECT c.corp_id, c.name, "
        "COALESCE(SUM(COALESCE(l.bio_exp,0)),0) AS be, "
        "COALESCE(SUM(COALESCE(l.infected_total,0)),0) AS sick "
        "FROM corps c "
        "LEFT JOIN corp_members m ON m.corp_id=c.corp_id "
        "LEFT JOIN labs l ON l.user_id=m.user_id "
        "GROUP BY c.corp_id, c.name "
        "ORDER BY be DESC, sick DESC, c.corp_id ASC "
        "LIMIT ?",
        (int(limit),)
    ) or []

def _top_corp_rows_chat(chat_id: int, limit: int):
    return db_all(
        "SELECT c.corp_id, c.name, "
        "COALESCE(SUM(COALESCE(l.bio_exp,0)),0) AS be, "
        "COALESCE(SUM(COALESCE(l.infected_total,0)),0) AS sick "
        "FROM corps c "
        "LEFT JOIN corp_members m ON m.corp_id=c.corp_id "
        "LEFT JOIN labs l ON l.user_id=m.user_id "
        "WHERE c.created_chat_id=? "
        "GROUP BY c.corp_id, c.name "
        "ORDER BY be DESC, sick DESC, c.corp_id ASC "
        "LIMIT ?",
        (int(chat_id), int(limit))
    ) or []

def render_top_users(limit: int, chat_id: int = 0) -> tuple[str, InlineKeyboardMarkup]:
    rows = _top_user_rows_chat(int(chat_id), int(limit)) if int(chat_id) != 0 else _top_user_rows(int(limit))
    title = "🔬 ТОП ЛАБОРАТОРИЙ ЧАТА ПО БИО-ОПЫТУ ЗАРАЖЁННЫХ:" if int(chat_id) != 0 else "🔬 ТОП ЛАБОРАТОРИЙ ПО БИО-ОПЫТУ ЗАРАЖЁННЫХ:"
    lines = [title]

    if not rows:
        lines.append("<blockquote>Нет данных.</blockquote>")
        return "\n".join(lines), kb_top_switch("U", int(chat_id), int(limit))

    lines.append("<blockquote expandable>")
    for i, r in enumerate(rows, 1):
        uid = int(r["user_id"])
        tag = public_user_tag(uid)
        lines.append(f"{i}. {tag} | {_fmt_k(int(r['be'] or 0))} опыт | {_fmt_k(int(r['sick'] or 0))} бол")
    lines.append("</blockquote>")
    return "\n".join(lines), kb_top_switch("U", int(chat_id), int(limit))

def render_top_diseases(limit: int, chat_id: int = 0) -> tuple[str, InlineKeyboardMarkup]:
    rows = _top_disease_rows_chat(int(chat_id), int(limit)) if int(chat_id) != 0 else _top_disease_rows(int(limit))
    title = "🔬 ТОП БОЛЕЗНЕЙ ЧАТА:" if int(chat_id) != 0 else "🔬 ТОП БОЛЕЗНЕЙ:"
    lines = [title]

    if not rows:
        lines.append("<blockquote>Нет данных.</blockquote>")
        return "\n".join(lines), kb_top_switch("D", int(chat_id), int(limit))

    lines.append("<blockquote expandable>")
    for i, r in enumerate(rows, 1):
        owner_id = int(r["user_id"])
        owner_un = (r["username"] or "")
        pname = (r["pname"] or "").strip()
        disease_name = f"«{h(pname)}»" if pname else "неизвестный патоген"
        clickable_disease = tg_mention(owner_id, disease_name, username=owner_un)
        lines.append(f"{i}. {clickable_disease} | {_fmt_k(int(r['sick'] or 0))} бол")
    lines.append("</blockquote>")
    return "\n".join(lines), kb_top_switch("D", int(chat_id), int(limit))

def render_top_corps(limit: int, chat_id: int = 0) -> tuple[str, InlineKeyboardMarkup]:
    rows = _top_corp_rows_chat(int(chat_id), int(limit)) if int(chat_id) != 0 else _top_corp_rows(int(limit))
    title = "🔬ТОП КОРПОРАЦИЙ ЧАТА:" if int(chat_id) != 0 else "🔬ТОП КОРПОРАЦИЙ:"
    lines = [title]

    if not rows:
        lines.append("<blockquote>Нет данных.</blockquote>")
        return "\n".join(lines), kb_top_switch("C", int(chat_id), int(limit))

    lines.append("<blockquote expandable>")
    for i, r in enumerate(rows, 1):
        corp_row = corp_by_id(int(r["corp_id"]))
        nm = corp_clickable_name(corp_row) if corp_row else corp_name_display((r["name"] or "").strip())
        lines.append(f"{i}. {nm} | {_fmt_k(int(r['be'] or 0))} опыт | {_fmt_k(int(r['sick'] or 0))} бол")
    lines.append("</blockquote>")
    return "\n".join(lines), kb_top_switch("C", int(chat_id), int(limit))

def handle_top_commands(message, parsed: "Parsed"):
    limit = _top_limit_from_args(parsed.args or "")

    if parsed.cmd == "top_users":
        text, rm = render_top_users(limit, 0)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

    if parsed.cmd == "top_diseases":
        text, rm = render_top_diseases(limit, 0)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

    if parsed.cmd == "top_corps":
        text, rm = render_top_corps(limit, 0)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

    if message.chat.type not in ("group", "supergroup"):
        bot.reply_to(message, "📑 Эта команда работает только в общем чате.")
        return

    chat_id = int(message.chat.id)

    if parsed.cmd == "top_users_chat":
        text, rm = render_top_users(limit, chat_id)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

    if parsed.cmd == "top_diseases_chat":
        text, rm = render_top_diseases(limit, chat_id)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

    if parsed.cmd == "top_corps_chat":
        text, rm = render_top_corps(limit, chat_id)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

def get_support_agents() -> List[sqlite3.Row]:
    return db_all("""
        SELECT sa.user_id, sa.role, sa.added_at, u.username, u.first_name, u.last_name, u.last_seen
        FROM support_agents sa
        LEFT JOIN users u ON u.user_id = sa.user_id
        WHERE sa.user_id<>?
          AND NOT EXISTS (
              SELECT 1 FROM bot_owners bo WHERE bo.user_id=sa.user_id
          )
        ORDER BY sa.added_at ASC
    """, (int(get_current_creator_id()),)) or []

def is_support(user_id: int) -> bool:
    uid = int(user_id)
    return is_agent(uid) or can_use_owner_commands(uid)

def can_manage_support(user_id: int) -> bool:
    """
    Совместимый wrapper для старых owner-only handler'ов.
    Теперь owner-команды доступны только владельцам.
    """
    return can_manage_agents(int(user_id))

def find_user_id_by_username(username: str) -> Optional[int]:
    username = (username or "").strip().lstrip("@").lower()
    if not username:
        return None

    row = db_one(
        "SELECT user_id FROM users "
        "WHERE username=? "
        "ORDER BY COALESCE(is_placeholder,0) ASC, COALESCE(last_seen,0) DESC, user_id DESC "
        "LIMIT 1",
        (username,)
    )
    if row:
        return int(row["user_id"])

    row = db_one("SELECT user_id FROM bot_bans WHERE username=? LIMIT 1", (username,))
    if row:
        return int(row["user_id"])

    return None

def _extract_public_username_token(token: str) -> str:
    s = (token or "").strip()

    if s.startswith("@"):
        uname = s[1:].strip()
    else:
        m = re.match(
            r"^(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z0-9_]{3,64})/?$",
            s,
            flags=re.IGNORECASE
        )
        if not m:
            return ""
        uname = m.group(1).strip()

    uname = re.sub(r"[^A-Za-z0-9_]", "", uname)
    return uname.lower()

def _alloc_placeholder_user_id() -> int:
    row = db_one("SELECT MIN(user_id) AS mn FROM users WHERE user_id < 0")
    mn = int(row["mn"] or 0) if row else 0
    if mn >= 0:
        return -1
    return int(mn) - 1

def _ensure_placeholder_user_by_uid(user_id: int) -> int:
    uid = int(user_id)
    row = get_user_row(uid)
    if row:
        if int(row["is_placeholder"] or 0) != 1:
            db_exec("UPDATE users SET is_placeholder=0 WHERE user_id=?", (uid,), commit=True)
        return uid

    db_exec(
        "INSERT INTO users(user_id, username, first_name, last_name, last_seen, is_placeholder) VALUES (?,?,?,?,?,1)",
        (uid, None, None, None, 0),
        commit=True
    )
    return uid

def _ensure_placeholder_user_by_username(username: str) -> int:
    uname = (username or "").strip().lstrip("@").lower()
    if not uname:
        return 0

    known = find_user_id_by_username(uname)
    if known is not None:
        return int(known)

    row = db_one(
        "SELECT user_id FROM users WHERE username=? AND COALESCE(is_placeholder,0)=1 LIMIT 1",
        (uname,)
    )
    if row:
        return int(row["user_id"])

    ph_id = _alloc_placeholder_user_id()
    db_exec(
        "INSERT INTO users(user_id, username, first_name, last_name, last_seen, is_placeholder) VALUES (?,?,?,?,?,1)",
        (int(ph_id), uname, None, None, 0),
        commit=True
    )
    return int(ph_id)

def _resolve_or_create_infect_target(token: str) -> Optional[int]:
    s = (token or "").strip()
    if not s:
        return None

    m = re.search(r"tg://openmessage\?user_id=(\d+)", s, flags=re.IGNORECASE)
    if m:
        return _ensure_placeholder_user_by_uid(int(m.group(1)))

    m = re.search(r"tg://user\?id=(\d+)", s, flags=re.IGNORECASE)
    if m:
        return _ensure_placeholder_user_by_uid(int(m.group(1)))

    if re.fullmatch(r"-?\d{1,20}", s):
        uid = int(s)
        row = get_user_row(uid)
        if row:
            return int(uid)
        if uid > 0 and len(str(uid)) >= 7:
            return _ensure_placeholder_user_by_uid(uid)
        return None

    uname = _extract_public_username_token(s)
    if uname:
        return _ensure_placeholder_user_by_username(uname)

    m = re.search(r"@([A-Za-z0-9_]{3,64})", s)
    if m:
        return _ensure_placeholder_user_by_username(m.group(1))

    m = re.search(
        r"(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z0-9_]{3,64})/?",
        s,
        flags=re.IGNORECASE
    )
    if m:
        return _ensure_placeholder_user_by_username(m.group(1))

    return None

def _raw_name_fallback(first_name: str, last_name: str) -> str:
    fn = _strip_invisible(first_name or "").strip()
    ln = _strip_invisible(last_name or "").strip()
    full = (fn + " " + ln).strip()

    if not full:
        return ""

    if _is_transparent_or_zalgo_only_name(full):
        return ""

    return full

def _is_transparent_or_zalgo_only_name(s: str) -> bool:
    """
    True только если имя после очистки:
    - пустое / состоит из transparent-like символов
    - или состоит только из combining marks (zalgo без базовых символов)
    Нормальные имена, цифры, буквы и пунктуацию не режем.
    """
    t = _strip_invisible(s or "")
    t = "".join(ch for ch in t if (ch not in _VARIATION_SELECTORS) and (not ch.isspace()))
    if not t:
        return True

    cleaned = []
    for ch in t:
        if ch in _BLANK_LIKE_CHARS:
            continue
        cleaned.append(ch)

    if not cleaned:
        return True

    only_marks = True
    for ch in cleaned:
        cat = unicodedata.category(ch)
        if cat not in ("Mn", "Mc", "Me") and not unicodedata.combining(ch):
            only_marks = False
            break

    return only_marks

def _safe_clickable_name_or_uid(name: str, uid: int) -> str:
    """
    Возвращает:
    - нормальное имя, если оно пригодно
    - uid строкой, если имя прозрачное/zalgo-only/пустое
    """
    nm = _strip_invisible(name or "").strip()
    if not nm or _is_transparent_or_zalgo_only_name(nm):
        return str(int(uid))
    return nm

def _best_known_display_by_uid(user_id: int) -> tuple[str, str, int]:
    uid = int(user_id)
    row = get_user_row(uid)

    if row:
        un = _normalize_username_for_link((row["username"] or ""))
        raw_disp = _raw_name_fallback(row["first_name"] or "", row["last_name"] or "")
        raw_disp = _safe_clickable_name_or_uid(raw_disp, uid)

        if raw_disp != str(uid):
            return raw_disp, un, uid

        if un:
            return un, un, uid

        return str(uid), "", uid

    cm = db_one(
        "SELECT username FROM chat_members "
        "WHERE user_id=? "
        "ORDER BY COALESCE(last_seen,0) DESC LIMIT 1",
        (uid,)
    )
    if cm:
        cm_un = _normalize_username_for_link((cm["username"] or ""))
        if cm_un:
            return cm_un, cm_un, uid

    if uid > 0:
        return str(uid), "", uid

    return "неизвестный пользователь", "", uid

def public_user_tag(user_id: int, force_standard: bool = False) -> str:
    uid = int(user_id)
    row = get_user_row(uid)

    alias = ""
    if (not force_standard) and (not _chat_name_ctx_force_standard()):
        alias = get_chat_user_name(_chat_name_ctx_chat_id(), uid)

    if row:
        un = _normalize_username_for_link((row["username"] or ""))

        if alias:
            return tg_mention(uid, alias, username=un)

        if int(row["is_placeholder"] or 0) == 1:
            if un:
                return tg_mention(uid, un, username=un)
            if uid > 0:
                return tg_mention(uid, str(uid))
            return "неизвестный пользователь"

        disp = (
            standard_display_name(row["first_name"] or "", row["last_name"] or "", row["username"] or "", uid)
            if force_standard
            else display_name(row["first_name"] or "", row["last_name"] or "", row["username"] or "", uid)
        )
        label = _safe_clickable_name_or_uid(disp, uid)
        return tg_mention(uid, label, username=un)

    disp, un, real_uid = _best_known_display_by_uid(uid)

    if alias and uid > 0:
        return tg_mention(uid, alias, username=un)

    if real_uid > 0:
        label = _safe_clickable_name_or_uid(disp, real_uid)
        return tg_mention(real_uid, label, username=un)

    if un:
        return tg_mention(real_uid, un, username=un)

    return "неизвестный пользователь"

def standard_user_tag(user_id: int) -> str:
    return public_user_tag(int(user_id), force_standard=True)

def rp_premium_emoji_html(emoji: str, premium_id: str) -> str:
    emo = re.sub(r"\s+", " ", str(emoji or "").strip())
    pid = str(premium_id or "").strip()

    if PREMIUM_EMOJI_ENABLED and pid:
        fallback = _rp_pick_single_fallback_emoji(emo) or "🔹"
        return f'<tg-emoji emoji-id="{h(pid)}">{h(fallback)}</tg-emoji>'

    return _rp_plain_emoji_html(emo)

def _rp_actor_tag(user_obj) -> str:
    uid = int(user_obj.id)
    un = (getattr(user_obj, "username", None) or "").strip()
    disp = display_name(
        getattr(user_obj, "first_name", "") or "",
        getattr(user_obj, "last_name", "") or "",
        un,
        uid
    )
    return tg_mention(uid, disp, username=un)

def resolve_rp_target(message, actor_id: int, args_text: str):
    if message.reply_to_message:
        if is_channel_sender_message(message.reply_to_message):
            return None, None

        u = getattr(message.reply_to_message, "from_user", None)
        if (
            u
            and not bool(getattr(u, "is_bot", False))
            and int(getattr(u, "id", 0) or 0) != int(actor_id)
        ):
            capture_user_context(message, u)
            return int(u.id), u

        tid = _pick_reply_target_id(message, exclude_user_ids={int(actor_id)})
        if tid is not None:
            return int(tid), None

        if (
            u
            and int(getattr(u, "id", 0) or 0) != int(actor_id)
        ):
            capture_user_context(message, u)
            return int(u.id), u

    full = (args_text or "").strip()
    if not full:
        return None, None

    tid = _resolve_single_target_from_text(full, _resolve_or_create_infect_target)
    if tid is not None:
        return int(tid), None

    return None, None

def _parse_rp_message(text: str, actor_id: int):
    raw = strip_bio_prefix((text or "").strip())
    if not raw:
        return None, "", ""

    first, _, comment = raw.partition("\n")
    first = first.strip()
    comment = comment.strip()

    actions = _all_rp_actions_for_user(int(actor_id))
    if not actions:
        return None, "", ""

    low = first.lower()

    for action in actions:
        trig = (action["trigger"] or "").strip().lower()
        if not trig:
            continue

        if low == trig:
            return action, "", comment

        if low.startswith(trig + " "):
            tail = first[len(action["trigger"]):].strip()
            return action, tail, comment

    return None, "", ""

def _parse_inline_rp_query(text: str, actor_id: int):
    raw = (text or "").strip()
    if not raw:
        return None, "", ""

    first, _, comment = raw.partition("\n")
    first = first.strip()
    comment = comment.strip()

    actions = _all_rp_actions_for_user(int(actor_id))
    if not actions:
        return None, "", ""

    low = first.lower()

    for action in actions:
        trig = (action["trigger"] or "").strip().lower()
        if not trig:
            continue

        if low == trig:
            return action, "", comment

        if low.startswith(trig + " "):
            tail = first[len(action["trigger"]):].strip()
            return action, tail, comment

    return None, "", ""

def _rp_emit_action_text(
    action: dict,
    actor_id: int,
    actor_tag: str,
    target_tag: str,
    extra_tail: str = "",
    comment_text: str = ""
) -> str:
    emo = rp_premium_emoji_html(action["emoji"], action["premium_id"])
    extra_tail = (extra_tail or "").strip()
    comment_text = (comment_text or "").strip()
    
    actor_gender = get_user_gender(int(actor_id))
    action_text = _rp_action_text_for_output(action, actor_gender=actor_gender)
    
    text = f"{emo}| {actor_tag} {h(action_text)} {target_tag}"
    if extra_tail:
        text += f" {h(extra_tail)}"
    if comment_text:
        text += f"\n💬 Комментарий: {h(comment_text)}"
    return text

def _rp_insert_event(action_key: str, actor_id: int, target_id: int):
    db_exec(
        "INSERT INTO rp_events(action_key, actor_id, target_id, created_at) VALUES (?,?,?,?)",
        (str(action_key), int(actor_id), int(target_id), int(now_ts())),
        commit=True
    )

def render_rp_stats_text(uid: int) -> str:
    actions = load_rp_actions()

    lines = ["🧾 Чеклист"]
    added = False

    for key, action in actions.items():
        stat1 = (action.get("stat1") or "").strip()
        stat2 = (action.get("stat2") or "").strip()

        if not stat1 and not stat2:
            continue

        emo = rp_premium_emoji_html(action["emoji"], action["premium_id"])

        if stat1:
            row = db_one(
                "SELECT COUNT(*) AS c FROM rp_events WHERE action_key=? AND actor_id=?",
                (str(key), int(uid))
            )
            cnt = int(row["c"] or 0) if row else 0
            lines.append(f"{emo}| {h(stat1)}: {cnt}")
            added = True

        if stat2:
            row = db_one(
                "SELECT COUNT(*) AS c FROM rp_events WHERE action_key=? AND target_id=?",
                (str(key), int(uid))
            )
            cnt = int(row["c"] or 0) if row else 0
            lines.append(f"{emo}| {h(stat2)}: {cnt}")
            added = True

    if not added:
        lines.append("<blockquote>Нет данных.</blockquote>")

    return "\n".join(lines)

def _create_rp_offer(actor_id: int, action_key: str, extra_tail: str = "", comment_text: str = "") -> int:
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute(
                "INSERT INTO rp_offers(actor_id, action_key, target_id, status, created_at, extra_tail, comment_text) "
                "VALUES (?,?,?,?,?,?,?)",
                (
                    int(actor_id),
                    str(action_key),
                    0,
                    "pending",
                    int(now_ts()),
                    str(extra_tail or "").strip(),
                    str(comment_text or "").strip(),
                )
            )
            conn.commit()
            return int(c.lastrowid)
        finally:
            try:
                c.close()
            except Exception:
                pass

def _merge_placeholder_to_real_user(tg_user):
    real_uid = int(tg_user.id)
    uname = ((getattr(tg_user, "username", None) or "").strip().lower())

    db_exec("UPDATE users SET is_placeholder=0 WHERE user_id=?", (real_uid,), commit=True)

    if not uname:
        return

    ph = db_one(
        "SELECT user_id FROM users "
        "WHERE username=? AND COALESCE(is_placeholder,0)=1 AND user_id<>? "
        "ORDER BY user_id ASC LIMIT 1",
        (uname, real_uid)
    )
    if not ph:
        return

    ph_uid = int(ph["user_id"])

    real_lab = db_one("SELECT COALESCE(lab_active,0) AS la FROM labs WHERE user_id=? LIMIT 1", (real_uid,))
    ph_lab = db_one(
        "SELECT COALESCE(bio_exp,0) AS be, COALESCE(fever_until_ts,0) AS fut, "
        "COALESCE(diseases_total,0) AS dt, COALESCE(fever_pathogen,'') AS fp "
        "FROM labs WHERE user_id=? LIMIT 1",
        (ph_uid,)
    )

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            if ph_lab:
                if (not real_lab) or int(real_lab["la"] or 0) == 0:
                    c.execute("DELETE FROM labs WHERE user_id=?", (real_uid,))
                    c.execute("UPDATE labs SET user_id=? WHERE user_id=?", (real_uid, ph_uid))
                else:
                    c.execute(
                        "UPDATE labs SET "
                        "bio_exp=MAX(COALESCE(bio_exp,0), ?), "
                        "fever_until_ts=MAX(COALESCE(fever_until_ts,0), ?), "
                        "diseases_total=MAX(COALESCE(diseases_total,0), ?), "
                        "fever_pathogen=CASE WHEN COALESCE(fever_pathogen,'')='' THEN ? ELSE fever_pathogen END "
                        "WHERE user_id=?",
                        (
                            int(ph_lab["be"] or 0),
                            int(ph_lab["fut"] or 0),
                            int(ph_lab["dt"] or 0),
                            str(ph_lab["fp"] or ""),
                            real_uid,
                        )
                    )
                    c.execute("DELETE FROM labs WHERE user_id=?", (ph_uid,))

            c.execute(
                "INSERT OR REPLACE INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name) "
                "SELECT attacker_id, ?, start_ts, end_ts, add_bio_res, next_payout_ts, counted, COALESCE(pathogen_name,'') "
                "FROM infections WHERE target_id=?",
                (real_uid, ph_uid)
            )
            c.execute("DELETE FROM infections WHERE target_id=?", (ph_uid,))

            c.execute(
                "INSERT OR IGNORE INTO infection_seen(attacker_id,target_id,first_ts) "
                "SELECT attacker_id, ?, first_ts FROM infection_seen WHERE target_id=?",
                (real_uid, ph_uid)
            )
            c.execute("DELETE FROM infection_seen WHERE target_id=?", (ph_uid,))

            c.execute(
                "INSERT OR REPLACE INTO infection_cooldowns(attacker_id,target_id,until_ts) "
                "SELECT attacker_id, ?, until_ts FROM infection_cooldowns WHERE target_id=?",
                (real_uid, ph_uid)
            )
            c.execute("DELETE FROM infection_cooldowns WHERE target_id=?", (ph_uid,))

            c.execute(
                "INSERT OR REPLACE INTO sabotage_cooldowns(attacker_id,target_id,until_ts) "
                "SELECT attacker_id, ?, until_ts FROM sabotage_cooldowns WHERE target_id=?",
                (real_uid, ph_uid)
            )
            c.execute("DELETE FROM sabotage_cooldowns WHERE target_id=?", (ph_uid,))

            c.execute("DELETE FROM users WHERE user_id=? AND COALESCE(is_placeholder,0)=1", (ph_uid,))
            c.execute("UPDATE users SET is_placeholder=0 WHERE user_id=?", (real_uid,))

            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _merge_placeholder_for_uid_if_possible(user_or_id):
    try:
        if hasattr(user_or_id, "id"):
            uid = int(getattr(user_or_id, "id"))
        else:
            uid = int(user_or_id)
    except Exception:
        return

    row = get_user_row(uid)
    if not row:
        return

    uname = ((row["username"] or "").strip().lower())
    if not uname:
        return

    fake = type("U", (), {})()
    fake.id = uid
    fake.username = uname
    fake.first_name = row["first_name"] or ""
    fake.last_name = row["last_name"] or ""
    _merge_placeholder_to_real_user(fake)

def get_name_restriction_row(user_id: int):
    return db_one(
        "SELECT user_id, "
        "user_locked, user_by, user_at, user_reason, "
        "lab_locked, lab_by, lab_at, lab_reason, "
        "pat_locked, pat_by, pat_at, pat_reason, "
        "corp_locked, corp_by, corp_at, corp_reason "
        "FROM user_name_restrictions WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )

def set_name_restriction(user_id: int, kind: str, locked: int, imposed_by: int, reason: str):
    uid = int(user_id)
    agent = int(imposed_by)
    reason = str(reason or "")[:50]
    now = now_ts()

    row = get_name_restriction_row(uid)
    cur = dict(row) if row else {
        "user_locked": 0, "user_by": 0, "user_at": 0, "user_reason": "",
        "lab_locked": 0, "lab_by": 0, "lab_at": 0, "lab_reason": "",
        "pat_locked": 0, "pat_by": 0, "pat_at": 0, "pat_reason": "",
        "corp_locked": 0, "corp_by": 0, "corp_at": 0, "corp_reason": "",
    }

    if kind == "user":
        cur["user_locked"] = int(locked)
        cur["user_by"] = agent if int(locked) == 1 else 0
        cur["user_at"] = now if int(locked) == 1 else 0
        cur["user_reason"] = reason if int(locked) == 1 else ""
    elif kind == "lab":
        cur["lab_locked"] = int(locked)
        cur["lab_by"] = agent if int(locked) == 1 else 0
        cur["lab_at"] = now if int(locked) == 1 else 0
        cur["lab_reason"] = reason if int(locked) == 1 else ""
    elif kind == "pat":
        cur["pat_locked"] = int(locked)
        cur["pat_by"] = agent if int(locked) == 1 else 0
        cur["pat_at"] = now if int(locked) == 1 else 0
        cur["pat_reason"] = reason if int(locked) == 1 else ""
    else:
        cur["corp_locked"] = int(locked)
        cur["corp_by"] = agent if int(locked) == 1 else 0
        cur["corp_at"] = now if int(locked) == 1 else 0
        cur["corp_reason"] = reason if int(locked) == 1 else ""

    if (
        int(cur["user_locked"]) == 0
        and int(cur["lab_locked"]) == 0
        and int(cur["pat_locked"]) == 0
        and int(cur["corp_locked"]) == 0
    ):
        db_exec("DELETE FROM user_name_restrictions WHERE user_id=?", (uid,), commit=True)
        return

    db_exec(
        "INSERT INTO user_name_restrictions("
        "user_id, "
        "user_locked, user_by, user_at, user_reason, "
        "lab_locked, lab_by, lab_at, lab_reason, "
        "pat_locked, pat_by, pat_at, pat_reason, "
        "corp_locked, corp_by, corp_at, corp_reason"
        ") VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "user_locked=excluded.user_locked, user_by=excluded.user_by, user_at=excluded.user_at, user_reason=excluded.user_reason, "
        "lab_locked=excluded.lab_locked, lab_by=excluded.lab_by, lab_at=excluded.lab_at, lab_reason=excluded.lab_reason, "
        "pat_locked=excluded.pat_locked, pat_by=excluded.pat_by, pat_at=excluded.pat_at, pat_reason=excluded.pat_reason, "
        "corp_locked=excluded.corp_locked, corp_by=excluded.corp_by, corp_at=excluded.corp_at, corp_reason=excluded.corp_reason",
        (
            uid,
            int(cur["user_locked"]), int(cur["user_by"]), int(cur["user_at"]), str(cur["user_reason"]),
            int(cur["lab_locked"]), int(cur["lab_by"]), int(cur["lab_at"]), str(cur["lab_reason"]),
            int(cur["pat_locked"]), int(cur["pat_by"]), int(cur["pat_at"]), str(cur["pat_reason"]),
            int(cur["corp_locked"]), int(cur["corp_by"]), int(cur["corp_at"]), str(cur["corp_reason"]),
        ),
        commit=True
    )

def _blacklist_collect_rows() -> list[dict]:
    out: Dict[int, dict] = {}

    bans = db_all(
        "SELECT user_id, banned_by, banned_at, reason, username, first_name, last_name "
        "FROM bot_bans ORDER BY banned_at DESC, user_id DESC"
    ) or []
    for r in bans:
        uid = int(r["user_id"])
        item = out.setdefault(uid, {
            "user_id": uid,
            "statuses": [],
            "reasons": [],
            "agents": [],
            "latest_ts": 0,
            "username": (r["username"] or "").strip(),
            "first_name": (r["first_name"] or "").strip(),
            "last_name": (r["last_name"] or "").strip(),
        })
        item["statuses"].append("блокировка в боте")
        if (r["reason"] or "").strip():
            item["reasons"].append((r["reason"] or "").strip())
        if int(r["banned_by"] or 0) > 0:
            item["agents"].append(int(r["banned_by"]))
        item["latest_ts"] = max(int(item["latest_ts"]), int(r["banned_at"] or 0))

    locks = db_all(
        "SELECT user_id, "
        "user_locked, user_by, user_at, user_reason, "
        "lab_locked, lab_by, lab_at, lab_reason, "
        "pat_locked, pat_by, pat_at, pat_reason, "
        "corp_locked, corp_by, corp_at, corp_reason "
        "FROM user_name_restrictions "
        "WHERE user_locked=1 OR lab_locked=1 OR pat_locked=1 OR corp_locked=1 "
        "ORDER BY user_id DESC"
    ) or []

    for r in locks:
        uid = int(r["user_id"])
        u = get_user_row(uid)
        item = out.setdefault(uid, {
            "user_id": uid,
            "statuses": [],
            "reasons": [],
            "agents": [],
            "latest_ts": 0,
            "username": ((u["username"] or "").strip() if u else ""),
            "first_name": ((u["first_name"] or "").strip() if u else ""),
            "last_name": ((u["last_name"] or "").strip() if u else ""),
        })

        if int(r["user_locked"] or 0) == 1:
            item["statuses"].append("имени пользователя")
            if (r["user_reason"] or "").strip():
                item["reasons"].append((r["user_reason"] or "").strip())
            if int(r["user_by"] or 0) > 0:
                item["agents"].append(int(r["user_by"]))
            item["latest_ts"] = max(int(item["latest_ts"]), int(r["user_at"] or 0))

        if int(r["lab_locked"] or 0) == 1:
            item["statuses"].append("имени лабы")
            if (r["lab_reason"] or "").strip():
                item["reasons"].append((r["lab_reason"] or "").strip())
            if int(r["lab_by"] or 0) > 0:
                item["agents"].append(int(r["lab_by"]))
            item["latest_ts"] = max(int(item["latest_ts"]), int(r["lab_at"] or 0))

        if int(r["pat_locked"] or 0) == 1:
            item["statuses"].append("имени патогена")
            if (r["pat_reason"] or "").strip():
                item["reasons"].append((r["pat_reason"] or "").strip())
            if int(r["pat_by"] or 0) > 0:
                item["agents"].append(int(r["pat_by"]))
            item["latest_ts"] = max(int(item["latest_ts"]), int(r["pat_at"] or 0))

        if int(r["corp_locked"] or 0) == 1:
            item["statuses"].append("названия корпорации")
            if (r["corp_reason"] or "").strip():
                item["reasons"].append((r["corp_reason"] or "").strip())
            if int(r["corp_by"] or 0) > 0:
                item["agents"].append(int(r["corp_by"]))
            item["latest_ts"] = max(int(item["latest_ts"]), int(r["corp_at"] or 0))

    rows = list(out.values())
    rows.sort(key=lambda x: (int(x["latest_ts"]), int(x["user_id"])), reverse=True)
    return rows

def _blacklist_cb(page: int) -> str:
    return f"{BLUI_TAG}:{int(page)}"

def _blacklist_parse_cb(data: str) -> Optional[int]:
    try:
        p = (data or "").split(":")
        if len(p) != 2 or p[0] != BLUI_TAG:
            return None
        return int(p[1])
    except Exception:
        return None

def _user_display_from_any(uid: int, username: str = "", first_name: str = "", last_name: str = "") -> str:
    uid = int(uid)
    u = get_user_row(uid)
    if u:
        un = (u["username"] or "").strip()
        fn = (u["first_name"] or "").strip()
        ln = (u["last_name"] or "").strip()
        return tg_mention(uid, standard_display_name(fn, ln, un, uid), username=un)

    un = (username or "").strip()
    fn = (first_name or "").strip()
    ln = (last_name or "").strip()
    if fn or ln or un:
        return tg_mention(uid, standard_display_name(fn, ln, un, uid), username=un)

    return f"<code>{uid}</code>"

def _agent_name_by_id(uid: int) -> str:
    u = get_user_row(int(uid))
    if u:
        un = (u["username"] or "").strip()
        disp = standard_display_name(u["first_name"] or "", u["last_name"] or "", un, int(uid))
        return tg_mention(int(uid), disp, username=un)
    return f"<code>{int(uid)}</code>"

def render_blacklist_text(page: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    rows = _blacklist_collect_rows()
    total = len(rows)

    if total <= 0:
        return "📑 ЧЁРНЫЙ СПИСОК:\nЗдесь пока пусто.", None

    total_pages = max(1, (total + TIMER_PAGE_SIZE - 1) // TIMER_PAGE_SIZE)
    page = max(1, min(int(page), total_pages))
    start = (page - 1) * TIMER_PAGE_SIZE
    part = rows[start:start + TIMER_PAGE_SIZE]

    lines = []
    lines.append("📑 ЧЁРНЫЙ СПИСОК:")
    lines.append("")
    lines.append("<blockquote expandable>")

    for idx, row in enumerate(part, start + 1):
        who = _user_display_from_any(
            int(row["user_id"]),
            username=str(row.get("username", "") or ""),
            first_name=str(row.get("first_name", "") or ""),
            last_name=str(row.get("last_name", "") or "")
        )
        statuses = " / ".join(dict.fromkeys([str(x) for x in row["statuses"] if str(x).strip()]))

        reasons = " | ".join(dict.fromkeys([str(x) for x in row["reasons"] if str(x).strip()]))

        agents_unique = []
        seen = set()
        for aid in row["agents"]:
            aid = int(aid)
            if aid > 0 and aid not in seen:
                seen.add(aid)
                agents_unique.append(_agent_name_by_id(aid))
        agent_text = " | ".join(agents_unique) if agents_unique else "—"

        lines.append(f"{idx}. {who} | {_fmt_ts(int(row['latest_ts'] or 0))}")
        lines.append(f"Ограничения: {h(statuses)}")
        if reasons:
            lines.append(f"🗒️ Причина: {h(reasons)}")
        lines.append(f"Агент: {agent_text}")

        if idx < start + len(part):
            lines.append("")

    lines.append("</blockquote>")

    kb = None
    if total_pages > 1:
        kb = InlineKeyboardMarkup(row_width=8)
        row_btns = []

        if page > 2:
            row_btns.append(InlineKeyboardButton("<<", callback_data=_blacklist_cb(1)))
        if page > 1:
            row_btns.append(InlineKeyboardButton("<", callback_data=_blacklist_cb(page - 1)))

        page_nums = [page]
        if page == 1:
            page_nums.extend([p for p in (2, 3, 4) if p <= total_pages])
        elif page == total_pages:
            page_nums = [p for p in (max(1, page - 3), max(1, page - 2), max(1, page - 1), page) if p <= total_pages]
        else:
            candidates = [page - 1, page, page + 1, page + 2]
            page_nums = [p for p in candidates if 1 <= p <= total_pages]

        page_nums = sorted(dict.fromkeys(page_nums))
        for p in page_nums:
            if p == page:
                row_btns.append(InlineKeyboardButton(f"·{p}·", callback_data=_blacklist_cb(page)))
            else:
                row_btns.append(InlineKeyboardButton(str(p), callback_data=_blacklist_cb(p)))

        if page < total_pages:
            row_btns.append(InlineKeyboardButton(">", callback_data=_blacklist_cb(page + 1)))
        if page < total_pages - 1:
            row_btns.append(InlineKeyboardButton(">>", callback_data=_blacklist_cb(total_pages)))

        kb.row(*row_btns)

    return "\n".join(lines), kb

USERS_PAGE_SIZE = 30

def _users_cb(page: int) -> str:
    return f"{USERSUI_TAG}:{int(page)}"

def _users_parse_cb(data: str) -> Optional[int]:
    try:
        p = (data or "").split(":")
        if len(p) != 2 or p[0] != USERSUI_TAG:
            return None
        return int(p[1])
    except Exception:
        return None

def _known_chats_cb(page: int) -> str:
    return f"{CHATSUI_TAG}:{int(page)}"

def _known_chats_parse_cb(data: str) -> Optional[int]:
    try:
        p = (data or "").split(":")
        if len(p) != 2 or p[0] != CHATSUI_TAG:
            return None
        return int(p[1])
    except Exception:
        return None

def _known_chats_collect_rows() -> list[dict]:
    rows = db_all(
        "SELECT q.chat_id, "
        "COALESCE(bg.title, '') AS title, "
        "COALESCE(bg.owner_id, 0) AS owner_id, "
        "COALESCE(bg.updated_at, 0) AS updated_at "
        "FROM ("
        "  SELECT chat_id FROM bot_group_chats WHERE COALESCE(is_active,0)=1 "
        "  UNION "
        "  SELECT chat_id FROM chat_members "
        ") q "
        "LEFT JOIN bot_group_chats bg ON bg.chat_id=q.chat_id "
        "ORDER BY COALESCE(bg.updated_at,0) DESC, q.chat_id ASC"
    ) or []

    out = []
    for r in rows:
        chat_id = int(r["chat_id"])
        title = (r["title"] or "").strip() or f"Чат {chat_id}"
        owner_id = int(r["owner_id"] or 0)

        if owner_id <= 0:
            try:
                sync_chat_admins(chat_id)
            except Exception:
                pass
            rr = db_one("SELECT COALESCE(owner_id,0) AS owner_id FROM bot_group_chats WHERE chat_id=?", (chat_id,))
            owner_id = int(rr["owner_id"] or 0) if rr else 0

        owner_tag = public_user_tag(owner_id, force_standard=True) if owner_id > 0 else "неизвестно"

        out.append({
            "chat_id": chat_id,
            "title": title,
            "owner_tag": owner_tag,
        })

    return out

def render_known_chats_text(page: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    rows = _known_chats_collect_rows()
    total = len(rows)

    if total <= 0:
        kb = InlineKeyboardMarkup()
        kb.row(InlineKeyboardButton("Пользователи", callback_data=_users_cb(1)))
        return "📑 Список известных чатов пуст.", kb

    total_pages = max(1, (total + USERS_PAGE_SIZE - 1) // USERS_PAGE_SIZE)
    page = max(1, min(int(page), total_pages))
    start = (page - 1) * USERS_PAGE_SIZE
    part = rows[start:start + USERS_PAGE_SIZE]

    lines = []
    lines.append("📑 Список известных чатов")
    lines.append("")
    lines.append("<blockquote expandable>")
    for idx, row in enumerate(part, start + 1):
        lines.append(f"{idx}. <b>{h(row['title'])}</b> | {row['owner_tag']}")
    lines.append("</blockquote>")

    kb = InlineKeyboardMarkup(row_width=8)
    row_btns = []

    if total_pages > 1:
        if page > 2:
            row_btns.append(InlineKeyboardButton("<<", callback_data=_known_chats_cb(1)))
        if page > 1:
            row_btns.append(InlineKeyboardButton("<", callback_data=_known_chats_cb(page - 1)))

        page_nums = []
        if total_pages <= 4:
            page_nums = list(range(1, total_pages + 1))
        elif page == 1:
            page_nums = [1, 2, 3, 4]
        elif page == total_pages:
            page_nums = [total_pages - 3, total_pages - 2, total_pages - 1, total_pages]
        else:
            page_nums = [max(1, page - 1), page, min(total_pages, page + 1), min(total_pages, page + 2)]
            page_nums = sorted(dict.fromkeys([p for p in page_nums if 1 <= p <= total_pages]))

        for p in page_nums:
            if p == page:
                row_btns.append(InlineKeyboardButton(f"·{p}·", callback_data=_known_chats_cb(page)))
            else:
                row_btns.append(InlineKeyboardButton(str(p), callback_data=_known_chats_cb(p)))

        if page < total_pages:
            row_btns.append(InlineKeyboardButton(">", callback_data=_known_chats_cb(page + 1)))
        if page < total_pages - 1:
            row_btns.append(InlineKeyboardButton(">>", callback_data=_known_chats_cb(total_pages)))

        kb.row(*row_btns)

    kb.row(InlineKeyboardButton("Пользователи", callback_data=_users_cb(1)))
    return "\n".join(lines), kb

def _users_collect_rows() -> list[dict]:
    rows = db_all(
        "SELECT u.user_id, u.username, u.first_name, u.last_name, u.last_seen, "
        "COALESCE(u.is_placeholder,0) AS is_placeholder, "
        "COALESCE(u.is_bot,0) AS is_bot, "
        "COALESCE(l.lab_active,0) AS lab_active "
        "FROM users u "
        "LEFT JOIN labs l ON l.user_id=u.user_id "
        "ORDER BY COALESCE(u.last_seen,0) DESC, u.user_id ASC"
    ) or []

    out = []
    for r in rows:
        uid = int(r["user_id"])
        un = (r["username"] or "").strip()
        fn = (r["first_name"] or "").strip()
        ln = (r["last_name"] or "").strip()
        is_bot = int(r["is_bot"] or 0)

        nm = "no name"
        if fn or ln or un:
            nm = standard_display_name(fn, ln, un, uid)
            if not nm or nm == str(uid):
                nm = _raw_name_fallback(fn, ln) or (f"@{un}" if un else "no name")

        if is_bot == 1:
            lab_text = "бот"
        else:
            lab_text = "есть лаба" if int(r["lab_active"] or 0) == 1 else "нет лабы"

        out.append({
            "user_id": uid,
            "name": nm,
            "username": f"@{un}" if un else "—",
            "lab_text": lab_text,
            "is_bot": is_bot,
        })
    return out

def render_users_text(page: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    rows = _users_collect_rows()
    total = len(rows)

    if total <= 0:
        return "📑 Список пользователей пуст.", None

    total_pages = max(1, (total + USERS_PAGE_SIZE - 1) // USERS_PAGE_SIZE)
    page = max(1, min(int(page), total_pages))
    start = (page - 1) * USERS_PAGE_SIZE
    part = rows[start:start + USERS_PAGE_SIZE]

    total_users = _users_total_count()
    total_bots = _users_bot_count()
    total_chats = _bot_group_chat_count()

    lines = []
    lines.append("📑 Список пользователей")
    lines.append("")
    lines.append(f"👥 Кол-во пользователей: {total_users}")
    lines.append(f"🤖 Кол-во ботов: {total_bots}")
    lines.append(f"🗨️ Кол-во чатов: {total_chats}")
    lines.append("")
    lines.append("<blockquote expandable>")

    for idx, row in enumerate(part, start + 1):
        lines.append(
            f"{idx}. {h(row['name'])}|{int(row['user_id'])}|{h(row['username'])}|{h(row['lab_text'])}"
        )

    lines.append("</blockquote>")

    kb = None
    if total_pages > 1:
        kb = InlineKeyboardMarkup(row_width=8)
        row_btns = []

        if page > 2:
            row_btns.append(InlineKeyboardButton("<<", callback_data=_users_cb(1)))
        if page > 1:
            row_btns.append(InlineKeyboardButton("<", callback_data=_users_cb(page - 1)))

        page_nums = []
        if total_pages <= 4:
            page_nums = list(range(1, total_pages + 1))
        elif page == 1:
            page_nums = [1, 2, 3, 4]
        elif page == total_pages:
            page_nums = [total_pages - 3, total_pages - 2, total_pages - 1, total_pages]
        else:
            page_nums = [max(1, page - 1), page, min(total_pages, page + 1), min(total_pages, page + 2)]
            page_nums = sorted(dict.fromkeys([p for p in page_nums if 1 <= p <= total_pages]))

        for p in page_nums:
            if p == page:
                row_btns.append(InlineKeyboardButton(f"·{p}·", callback_data=_users_cb(page)))
            else:
                row_btns.append(InlineKeyboardButton(str(p), callback_data=_users_cb(p)))

        if page < total_pages:
            row_btns.append(InlineKeyboardButton(">", callback_data=_users_cb(page + 1)))
        if page < total_pages - 1:
            row_btns.append(InlineKeyboardButton(">>", callback_data=_users_cb(total_pages)))

        kb.row(*row_btns)

    if kb is None:
        kb = InlineKeyboardMarkup()
    kb.row(InlineKeyboardButton("Известные чаты", callback_data=_known_chats_cb(1)))

    return "\n".join(lines), kb

def build_agents_panel_text(user_id: int) -> str:
    uid = int(user_id)
    self_row = get_user_row(uid)
    self_name = (
        display_name(
            self_row["first_name"] or "",
            self_row["last_name"] or "",
            self_row["username"] or "",
            int(uid)
        ) if self_row else str(uid)
    )

    if is_creator(uid):
        role_word = "создатель"
    elif is_owner(uid):
        role_word = "старший агент"
    else:
        role_word = "агент"

    owner_rows = _panel_owner_rows(uid)
    owner_online, owner_offline = split_agents_by_online(owner_rows)

    agent_rows = [a for a in get_support_agents() if int(a["user_id"]) != uid]
    agent_online, agent_offline = split_agents_by_online(agent_rows)

    lines = []
    lines.append(f"🔬 Приветствуем вас, {role_word} <b>{h(self_name)}</b>, в {h(BOT_TITLE)}")

    lines.append("💎 <b>Создатель и старшие агенты</b>")
    if not owner_online and not owner_offline:
        lines.append("Список пока пуст.")
    else:
        if owner_online:
            lines.append("🟢 Онлайн")
            for a in owner_online:
                role_txt = str(a.get('role_text', '')).strip()
                prefix = f"{role_txt.capitalize()}: " if role_txt else ""
                lines.append(prefix + format_agent_line(a))
        if owner_offline:
            lines.append("🔘 Оффлайн")
            for a in owner_offline:
                role_txt = str(a.get('role_text', '')).strip()
                prefix = f"{role_txt.capitalize()}: " if role_txt else ""
                lines.append(prefix + format_agent_line(a))

    lines.append("")
    lines.append("👨‍⚕️ <b>Агенты техподдержки</b>")
    if not agent_online and not agent_offline:
        lines.append("Список пока пуст.")
    else:
        if agent_online:
            lines.append("🟢 Онлайн")
            for a in agent_online:
                lines.append(format_agent_line(a))
        if agent_offline:
            lines.append("🔘 Оффлайн")
            for a in agent_offline:
                lines.append(format_agent_line(a))

    lines.append("")
    lines.append("💬 Следующие доступные Вам команды:")
    lines.append("<blockquote expandable>")

    if is_support(uid):
        lines.append("📒 Раздел агента техподдержки")
        lines.append("/bot_ban + {причина с новой строки} — заблокировать пользователя")
        lines.append("/bot_unban — разблокировать пользователя")
        lines.append("/remake_lab — восстановить лабораторию")
        lines.append("/delete — удалить пользователя из db")
        lines.append("<code>/+lab_name</code> | <code>/-lab_name</code> + {причина с новой строки} — разрешает/запрещает имена лаборатории для пользователя")
        lines.append("<code>/+pat_name</code> | <code>/-pat_name</code> + {причина с новой строки} — разрешает/запрещает имена патогена для пользователя")
        lines.append("<code>/+user_name</code> | <code>/-user_name</code> + {причина с новой строки} — разрешает/запрещает смену имени для пользователя")
        lines.append("<code>/+corp_name</code> | <code>/-corp_name</code> + {причина с новой строки} — разрешает/запрещает имена корпорации для пользователя")
        lines.append("/blacklist — список пользователей с ограничениями")
        lines.append("/users — список всех пользователей")
        lines.append("")

    if can_use_owner_commands(uid):
        lines.append("📒 Раздел старшего агента")
        lines.append("/agent — назначить агента техподдержки")
        lines.append("/agent_remove — снять права агента техподдержки")
        lines.append("/its + {ссылка} + {<code>бот</code>|<code>юзер</code>} — ручное редактирование списка")
        lines.append("")
        lines.append("⚔️ Дуэль")
        lines.append("/duel_cof_break — изменить 🪃")
        lines.append("/duel_cof_break_bon — изменить 🪃 бонус")
        lines.append("/duel_cof_aim — изменить 👁️‍🗨️ бонус")
        lines.append("/duel_cof_base_pts — изменить шанс попадания")
        lines.append("/duel_rounds — изменить кол-во раундов")
        lines.append("/duel_cof_stats — информация по переменным дуэлей")
        lines.append("")
        lines.append("🦠 Формула заразности") 
        lines.append("/edit_k — изменить k")
        lines.append("/edit_b — изменить β")
        lines.append("/cof_inf_stats — информация по переменным заражения")
        lines.append("")
        lines.append("💾 Data Base")
        lines.append("/db_fife_stat — параметры базы данных")
        lines.append("/db_fife_msg + {период} — автосэйв таймер")
        lines.append("/db_fife — файл базы данных")
        lines.append("/db_fife_upd — обновить базу данных")
        lines.append("")
        lines.append("🎁 Раздел промокоды:")
        lines.append("/promocode_generate — генерация случайного временного промокода")
        lines.append("/promocode_create — создание промокода")
        lines.append("/promocode_all — список всех промокодов")
        lines.append("/promocode_delete — удалить промокод")
        lines.append("")

    if is_creator(uid):
        lines.append("📒 Раздел создателя")
        lines.append("/my_owner — выдать себе права старшего агента")
        lines.append("/my_owner_remove — снять с себя права старшего агента")
        lines.append("/owner — назначить старшего агента")
        lines.append("/owner_remove — снять права старшего агента")

    lines.append("</blockquote>")
    return "\n".join(lines)

def get_bot_ban_row(user_id: int):
    row = db_one(
        "SELECT user_id, banned_by, banned_at, until_ts, reason "
        "FROM bot_bans WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )
    if not row:
        return None

    until_ts = int(row["until_ts"] or 0)
    if until_ts > 0 and until_ts <= now_ts():
        db_exec("DELETE FROM bot_bans WHERE user_id=?", (int(user_id),), commit=True)
        return None

    return row

def is_bot_banned(user_id: int) -> bool:
    return get_bot_ban_row(int(user_id)) is not None

def render_bot_ban_text(user_id: int) -> str:
    row = get_bot_ban_row(int(user_id))
    if not row:
        return "⛔ Доступ к боту ограничен."

    reason = (row["reason"] or "").strip()
    text = "⛔ Доступ к боту ограничен."
    if reason:
        text += f"\n\n🗒️ Причина: {h(reason)}"
    return text

def _resolve_admin_target_and_reason(message, parsed: "Parsed"):
    first_line, _body = _timer_first_line_and_body(message.text or "")
    fl = first_line.strip()
    if fl.startswith("/") or fl.startswith("."):
        fl = fl[1:].strip()

    reason = _timer_parse_reason_from_message(message.text or "")

    if message.reply_to_message:
        actor_id = int(getattr(getattr(message, "from_user", None), "id", 0) or 0)
        u = getattr(message.reply_to_message, "from_user", None)

        if (
            u
            and not bool(getattr(u, "is_bot", False))
            and int(getattr(u, "id", 0) or 0) != actor_id
        ):
            return int(u.id), u, reason

        tid = _pick_reply_target_id(message, exclude_user_ids=None)
        if tid is not None:
            return int(tid), None, reason

        if u and not bool(getattr(u, "is_bot", False)):
            return int(u.id), u, reason

    parts = fl.split(None, 1)
    if len(parts) < 2:
        return None, None, reason

    target_expr = parts[1].strip()
    target_id = resolve_target_id(target_expr)

    if target_id is None:
        s = target_expr.strip()

        if parsed.cmd == "bot_unban":
            if s.isdigit():
                target_id = int(s)
            elif s.startswith("@"):
                uname = s.lstrip("@").strip().lower()
                r = db_one(
                    "SELECT user_id FROM bot_bans WHERE lower(COALESCE(username,''))=? LIMIT 1",
                    (uname,)
                )
                if r:
                    target_id = int(r["user_id"])

    return target_id, None, reason

def _purge_user_for_bot_ban(user_id: int):
    uid = int(user_id)

    try:
        _corp_transfer_on_lab_delete(uid)
    except Exception:
        pass

    reqs = db_all("SELECT request_id FROM corp_requests WHERE user_id=?", (uid,)) or []
    for r in reqs:
        db_exec("DELETE FROM corp_request_msgs WHERE request_id=?", (int(r["request_id"]),), commit=True)

    db_exec("DELETE FROM corp_requests WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM corp_invites WHERE user_id=? OR invited_by=?", (uid, uid), commit=True)
    db_exec("DELETE FROM corp_members WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM infections WHERE attacker_id=? OR target_id=?", (uid, uid), commit=True)
    db_exec("DELETE FROM infection_seen WHERE attacker_id=? OR target_id=?", (uid, uid), commit=True)
    db_exec("DELETE FROM infection_cooldowns WHERE attacker_id=? OR target_id=?", (uid, uid), commit=True)
    db_exec("DELETE FROM sabotage_cooldowns WHERE attacker_id=? OR target_id=?", (uid, uid), commit=True)

    db_exec("DELETE FROM autoanswer_used_reports WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM autoanswer_state WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM lab_delete_pending WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM report_state WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM corp_notify_prefs WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM chat_members WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM support_agents WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM labs WHERE user_id=?", (uid,), commit=True)

    try:
        delete_deleted_lab_snapshot(uid)
    except Exception:
        pass
    try:
        _deleted_db_exec("DELETE FROM deleted_labs_log WHERE user_id=?", (uid,), commit=True)
    except Exception:
        pass

def _purge_user_for_delete(user_id: int):
    uid = int(user_id)

    _purge_user_for_bot_ban(uid)

    db_exec("DELETE FROM users WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM bot_bans WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM bot_owners WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM balance_chain_state WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM quick_infect_prefs WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM user_timers WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM db_file_msg_schedule WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM db_file_exports WHERE requested_by=?", (uid,), commit=True)

    db_exec("DELETE FROM user_name_restrictions WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM chat_user_names WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM personal_rp_actions WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM rp_offers WHERE actor_id=? OR target_id=?", (uid, uid), commit=True)
    db_exec("DELETE FROM rp_events WHERE actor_id=? OR target_id=?", (uid, uid), commit=True)

    db_exec("DELETE FROM promo_uses WHERE user_id=?", (uid,), commit=True)

    db_exec("DELETE FROM duel_stats WHERE user_id=?", (uid,), commit=True)
    db_exec("DELETE FROM duel_bets WHERE bettor_id=? OR candidate_id=?", (uid, uid), commit=True)
    db_exec("DELETE FROM duel_invites WHERE challenger_id=? OR target_id=?", (uid, uid), commit=True)
    db_exec(
        "DELETE FROM duels WHERE challenger_id=? OR target_id=? OR winner_id=? OR loser_id=? OR current_turn_user_id=?",
        (uid, uid, uid, uid, uid),
        commit=True
    )

    db_exec("UPDATE bot_group_chats SET owner_id=0 WHERE owner_id=?", (uid,), commit=True)

def handle_admin_service_commands(message, parsed: "Parsed"):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    if message.chat.type != "private":
        return

    if not is_support(uid):
        return

    target_id, target_user_obj, reason = _resolve_admin_target_and_reason(message, parsed)
    token = ((parsed.args or "").split()[0] if (parsed.args or "").strip() else "")

    if parsed.cmd in ("bot_ban", "remake_lab"):
        if is_bot_target(target_id, target_user_obj, token):
            bot.reply_to(message, bot_cannot_have("блокировки в боте"))
            return

    if target_id is None:
        bot.reply_to(message, "📑 Укажите пользователя через @username, user_id или reply.")
        return

    if int(target_id) == int(get_current_creator_id()) and parsed.cmd == "bot_ban":
        bot.reply_to(message, "📑 У меня нет такой власти(")
        return

    if parsed.cmd == "bot_ban":
        snap_username = ""
        snap_first_name = ""
        snap_last_name = ""

        if target_user_obj is not None:
            try:
                upsert_user(target_user_obj)
            except Exception:
                pass

            snap_username = ((getattr(target_user_obj, "username", None) or "").strip().lower())
            snap_first_name = ((getattr(target_user_obj, "first_name", None) or "").strip())
            snap_last_name = ((getattr(target_user_obj, "last_name", None) or "").strip())
        else:
            urow = get_user_row(int(target_id))
            if urow:
                snap_username = ((urow["username"] or "").strip().lower())
                snap_first_name = ((urow["first_name"] or "").strip())
                snap_last_name = ((urow["last_name"] or "").strip())

        try:
            _purge_user_for_bot_ban(int(target_id))
            db_exec(
                "INSERT OR REPLACE INTO bot_bans(user_id, banned_by, banned_at, until_ts, reason, username, first_name, last_name) "
                "VALUES (?,?,?,?,?,?,?,?)",
                (
                    int(target_id),
                    int(uid),
                    int(now_ts()),
                    0,
                    str(reason or ""),
                    str(snap_username or ""),
                    str(snap_first_name or ""),
                    str(snap_last_name or ""),
                ),
                commit=True
            )
        except Exception as e:
            send_error_report("bot_ban", e)
            bot.reply_to(message, "📑 Не удалось заблокировать пользователя в боте.")
            return

        bot.reply_to(
            message,
            f"✅ Пользователь <code>{_corp_actor_tag(int(target_id))}</code> заблокирован в боте.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "bot_unban":
        rc = db_exec("DELETE FROM bot_bans WHERE user_id=?", (int(target_id),), commit=True)
        if int(rc or 0) <= 0:
            bot.reply_to(message, "📑 Этот пользователь не заблокирован в боте.")
            return

        bot.reply_to(message, f"✅ Пользователь <code>{int(target_id)}</code> разблокирован в боте.", parse_mode="HTML")
        return

    if parsed.cmd == "remake_lab":
        try:
            ok, text = _restore_deleted_lab(int(target_id), support_mode=True)
        except Exception as e:
            send_error_report("remake_lab", e)
            bot.reply_to(message, "📑 Не удалось восстановить Лабораторию.")
            return

        if not ok:
            bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
            return

        bot.reply_to(
            message,
            f"✅ Лаборатория пользователя <code>{int(target_id)}</code> восстановлена через поддержку.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

def _fmt_file_size(num: int) -> str:
    n = int(num or 0)
    units = ["B", "KB", "MB", "GB", "TB"]
    i = 0
    x = float(n)
    while x >= 1024.0 and i < len(units) - 1:
        x /= 1024.0
        i += 1
    s = f"{x:.2f}".rstrip("0").rstrip(".")
    return f"{s} {units[i]}"

def _path_size(path: str) -> int:
    try:
        return int(os.path.getsize(path))
    except Exception:
        return 0

def _db_limit_bytes_for_path(path: str) -> int:
    c = None
    try:
        c = sqlite3.connect(path, check_same_thread=False)
        row1 = c.execute("PRAGMA page_size;").fetchone()
        row2 = c.execute("PRAGMA wal_autocheckpoint;").fetchone()
        page_size = int(row1[0] or 0) if row1 else 0
        wal_pages = int(row2[0] or 0) if row2 else 0
        return int(page_size * wal_pages)
    except Exception:
        return 0
    finally:
        try:
            if c is not None:
                c.close()
        except Exception:
            pass

def _db_schedule_row(user_id: int):
    return db_one(
        "SELECT user_id, repeat_spec, next_run_ts, updated_at "
        "FROM db_file_msg_schedule WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )

DB_FILE_MSG_MIN_SECONDS = 12 * 3600
DB_FILE_MSG_MAX_SECONDS = 30 * 86400

def _db_schedule_clear(user_id: int):
    db_exec(
        "DELETE FROM db_file_msg_schedule WHERE user_id=?",
        (int(user_id),),
        commit=True
    )

def _db_schedule_total_seconds(spec: dict) -> int:
    if not spec:
        return 0

    return int(
        int(spec.get("months", 0) or 0) * 30 * 86400
        + int(spec.get("weeks", 0) or 0) * 7 * 86400
        + int(spec.get("days", 0) or 0) * 86400
        + int(spec.get("hours", 0) or 0) * 3600
        + int(spec.get("minutes", 0) or 0) * 60
    )

def _db_schedule_validate_spec(spec: dict) -> tuple[bool, str]:
    total_sec = _db_schedule_total_seconds(spec)

    if total_sec < DB_FILE_MSG_MIN_SECONDS:
        return False, "📑 Минимальный период автосэйва — 12 часов."

    if total_sec > DB_FILE_MSG_MAX_SECONDS:
        return False, "📑 Максимальный период автосэйва — 1 месяц."

    return True, ""

def _dbstat_cb(user_id: int, action: str) -> str:
    return f"{DBSTATUI_TAG}:{int(user_id)}:{str(action or '').strip().upper()}"

def _dbstat_parse_cb(data: str):
    try:
        parts = (data or "").split(":")
        if len(parts) != 3 or parts[0] != DBSTATUI_TAG:
            return None
        return {
            "user_id": int(parts[1]),
            "action": (parts[2] or "").strip().upper(),
        }
    except Exception:
        return None

def kb_db_file_stat(owner_id: int):
    row = _db_schedule_row(int(owner_id))
    next_send_ts = int(row["next_run_ts"] or 0) if row else 0

    kb = InlineKeyboardMarkup(row_width=2)

    if next_send_ts > 0:
        kb.row(
            _ikb(
                "Сбросить автосэйв",
                callback_data=_dbstat_cb(int(owner_id), "RESET"),
                style="danger"
            ),
            _ikb(
                "Список db_id",
                callback_data=_dbstat_cb(int(owner_id), "LIST"),
                style="primary"
            )
        )
    else:
        kb.add(
            _ikb(
                "Список db_id",
                callback_data=_dbstat_cb(int(owner_id), "LIST"),
                style="primary"
            )
        )

    return kb

def _db_schedule_set(user_id: int, spec: dict):
    next_run_ts = int(_timer_apply_period(datetime.fromtimestamp(now_ts()), spec).timestamp())
    db_exec(
        "INSERT INTO db_file_msg_schedule(user_id, repeat_spec, next_run_ts, updated_at) VALUES (?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET repeat_spec=excluded.repeat_spec, next_run_ts=excluded.next_run_ts, updated_at=excluded.updated_at",
        (int(user_id), json.dumps(spec or {}, ensure_ascii=False), int(next_run_ts), int(now_ts())),
        commit=True
    )

def _db_schedule_reschedule(user_id: int, spec: dict, base_ts: int):
    dt = datetime.fromtimestamp(int(base_ts))
    nxt = _timer_apply_period(dt, spec)
    nowv = int(now_ts())
    while int(nxt.timestamp()) <= nowv:
        nxt = _timer_apply_period(nxt, spec)

    db_exec(
        "UPDATE db_file_msg_schedule SET next_run_ts=?, updated_at=? WHERE user_id=?",
        (int(nxt.timestamp()), int(nowv), int(user_id)),
        commit=True
    )

def _db_snapshot_copy(src_path: str, prefix: str) -> str:
    if not os.path.exists(src_path):
        return ""

    tmp_path = os.path.join(DATA_DIR, f"{prefix}_{int(now_ts())}.db")
    try:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
    except Exception:
        pass

    ok = _sqlite_backup_file(src_path, tmp_path)
    return tmp_path if ok and os.path.exists(tmp_path) else ""

def _db_export_source_title(source_kind: str) -> str:
    kind = str(source_kind or "").strip().upper()
    return "Backup" if kind == "BACKUP" else "Основная база данных"

def _db_file_export_cb(user_id: int, source_kind: str) -> str:
    return f"{DBFILEUI_TAG}:{int(user_id)}:{str(source_kind or '').strip().upper()}"

def _db_file_export_parse_cb(data: str):
    try:
        parts = (data or "").split(":")
        if len(parts) != 3 or parts[0] != DBFILEUI_TAG:
            return None
        return {
            "user_id": int(parts[1]),
            "source_kind": (parts[2] or "").strip().upper(),
        }
    except Exception:
        return None

def kb_db_file_export_choice(user_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        _ikb(
            "Основная база данных",
            callback_data=_db_file_export_cb(int(user_id), "MAIN"),
            style="primary"
        ),
        _ikb(
            "Backup",
            callback_data=_db_file_export_cb(int(user_id), "BACKUP"),
            style="primary"
        )
    )
    return kb

def _copy_file_to_temp(src_path: str, prefix: str, suffix: str = "") -> str:
    if not src_path or not os.path.exists(src_path):
        return ""

    suf = str(suffix or "").strip()
    if not suf:
        _, ext = os.path.splitext(src_path)
        suf = ext or ""

    tmp_path = os.path.join(
        DATA_DIR,
        f"{prefix}_{int(now_ts())}_{random.randint(1000, 9999)}{suf}"
    )

    try:
        with open(src_path, "rb") as src, open(tmp_path, "wb") as dst:
            dst.write(src.read())
        return tmp_path
    except Exception:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        return ""

def _db_export_collect_parts(source_kind: str):
    kind = str(source_kind or "").strip().upper()
    parts = []
    temp_paths = []

    if kind == "MAIN":
        with DB_LOCK:
            try:
                conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
            except Exception:
                pass

            main_copy = _copy_file_to_temp(DB_PATH, "db_export_main", ".db")
            wal_copy = ""
            if _path_size(DB_PATH + "-wal") > 0:
                wal_copy = _copy_file_to_temp(DB_PATH + "-wal", "db_export_main_wal", ".db-wal")

        deleted_copy = _db_snapshot_copy(DELETED_DB_PATH, "db_export_deleted")

        if main_copy:
            parts.append((main_copy, "bio_war.db"))
            temp_paths.append(main_copy)

        if wal_copy:
            parts.append((wal_copy, "bio_war.db-wal"))
            temp_paths.append(wal_copy)

        if deleted_copy:
            parts.append((deleted_copy, "deleted_labs.db"))
            temp_paths.append(deleted_copy)

        if not parts:
            return [], temp_paths, "📑 Не удалось подготовить текущую базу данных."

        return parts, temp_paths, ""

    if kind == "BACKUP":
        main_copy = _copy_file_to_temp(DB_BACKUP_MAIN_PATH, "db_export_backup_main", ".db")
        wal_copy = ""
        if _path_size(DB_BACKUP_MAIN_WAL_PATH) > 0:
            wal_copy = _copy_file_to_temp(DB_BACKUP_MAIN_WAL_PATH, "db_export_backup_wal", ".db-wal")
        deleted_copy = _copy_file_to_temp(DB_BACKUP_DELETED_PATH, "db_export_backup_deleted", ".db")

        if main_copy:
            parts.append((main_copy, "bio_war.db"))
            temp_paths.append(main_copy)

        if wal_copy:
            parts.append((wal_copy, "bio_war.db-wal"))
            temp_paths.append(wal_copy)

        if deleted_copy:
            parts.append((deleted_copy, "deleted_labs.db"))
            temp_paths.append(deleted_copy)

        if not parts:
            return [], temp_paths, "📑 Backup ещё не создан."

        return parts, temp_paths, ""

    return [], temp_paths, "📑 Неизвестный тип источника базы данных."

def _db_export_create_row(source_kind: str, requested_by: int, request_text: str) -> int:
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT INTO db_file_exports(source_kind, archive_path, requested_by, created_at, request_text) "
                "VALUES (?,?,?,?,?)",
                (
                    str(source_kind or "").strip().upper(),
                    "",
                    int(requested_by),
                    int(now_ts()),
                    str(request_text or "").strip(),
                )
            )
            export_id = int(c.lastrowid or 0)
            conn.commit()
            return export_id
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _db_export_update_path(db_id: int, archive_path: str):
    db_exec(
        "UPDATE db_file_exports SET archive_path=? WHERE db_id=?",
        (str(archive_path or ""), int(db_id)),
        commit=True
    )

def _db_export_delete_row(db_id: int):
    db_exec("DELETE FROM db_file_exports WHERE db_id=?", (int(db_id),), commit=True)

def _db_export_archive_path(db_id: int, source_kind: str) -> str:
    kind = str(source_kind or "").strip().upper()
    stem = "backup" if kind == "BACKUP" else "main"
    return os.path.join(DB_EXPORTS_DIR, f"db_{stem}_{int(db_id)}.zip")

def _build_db_export_archive(db_id: int, source_kind: str) -> tuple[bool, str, str]:
    parts, temp_paths, err = _db_export_collect_parts(source_kind)
    if not parts:
        for p in temp_paths:
            try:
                if p and os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass
        return False, "", err or "📑 Не удалось подготовить архив базы данных."

    archive_path = _db_export_archive_path(int(db_id), source_kind)

    try:
        try:
            if os.path.exists(archive_path):
                os.remove(archive_path)
        except Exception:
            pass

        with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
            for src_path, arcname in parts:
                if src_path and os.path.exists(src_path):
                    zf.write(src_path, arcname=arcname)

        if not os.path.exists(archive_path):
            return False, "", "📑 Не удалось собрать архив базы данных."

        return True, archive_path, ""

    finally:
        for p in temp_paths:
            try:
                if p and os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass

def _db_export_row_by_id(db_id: int):
    return db_one(
        "SELECT db_id, source_kind, archive_path, requested_by, created_at, request_text "
        "FROM db_file_exports WHERE db_id=? LIMIT 1",
        (int(db_id),)
    )

def _db_upd_safe_basename(name: str) -> str:
    base = os.path.basename(str(name or "").replace("\\", "/")).strip()
    if not base:
        base = "db_file.bin"
    base = re.sub(r"[^A-Za-zА-Яа-я0-9._-]+", "_", base)
    return base or "db_file.bin"

def _db_upd_temp_path(prefix: str, name: str) -> str:
    return os.path.join(
        DB_IMPORTS_DIR,
        f"{prefix}_{int(now_ts())}_{random.randint(1000, 9999)}_{_db_upd_safe_basename(name)}"
    )

def _db_upd_remove_path(path: str):
    try:
        if not path:
            return
        if os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)
        elif os.path.exists(path):
            os.remove(path)
    except Exception:
        pass

def _db_upd_download_document(doc) -> str:
    tg_file = bot.get_file(doc.file_id)
    raw = bot.download_file(tg_file.file_path)

    file_name = getattr(doc, "file_name", "") or "db_file.bin"
    local_path = _db_upd_temp_path("dbupd", file_name)

    with open(local_path, "wb") as f:
        f.write(raw)

    return local_path

def _sqlite_table_names(path: str) -> set[str]:
    names = set()
    c = None
    try:
        c = sqlite3.connect(path, check_same_thread=False)
        rows = c.execute(
            "SELECT name FROM sqlite_master "
            "WHERE type='table' AND name NOT LIKE 'sqlite_%'"
        ).fetchall()
        for r in rows:
            try:
                names.add(str(r[0]))
            except Exception:
                pass
    except Exception:
        return set()
    finally:
        try:
            if c is not None:
                c.close()
        except Exception:
            pass
    return names

def _db_upd_sqlite_kind(path: str) -> str:
    if not path or not os.path.exists(path):
        return ""

    if not _sqlite_file_integrity_ok(path):
        return ""

    tables = _sqlite_table_names(path)

    if "labs" in tables and "users" in tables:
        return "MAIN"

    if "deleted_labs" in tables:
        return "DELETED"

    return ""

def _db_upd_collect_source_documents(message):
    docs = []
    seen = set()

    def _add_doc(msg):
        if not msg:
            return
        doc = getattr(msg, "document", None)
        if not doc:
            return
        fid = str(getattr(doc, "file_id", "") or "")
        if fid and fid not in seen:
            seen.add(fid)
            docs.append(doc)

    _add_doc(message)
    _add_doc(getattr(message, "reply_to_message", None))
    return docs

def _db_upd_resolve_local_files(local_paths: list[str]) -> tuple[bool, dict, list[str], str]:
    cleanup_paths: list[str] = []

    zip_paths = [p for p in local_paths if str(p).lower().endswith(".zip")]
    if zip_paths:
        zip_path = zip_paths[0]
        extract_dir = _db_upd_temp_path("dbupd_zip", "extract")
        os.makedirs(extract_dir, exist_ok=True)
        cleanup_paths.append(extract_dir)

        extracted = []
        try:
            with zipfile.ZipFile(zip_path, "r") as zf:
                for info in zf.infolist():
                    if info.is_dir():
                        continue

                    base = _db_upd_safe_basename(info.filename)
                    low = base.lower()
                    if not (
                        low.endswith(".db")
                        or low.endswith(".db-wal")
                        or low.endswith(".wal")
                    ):
                        continue

                    dst = os.path.join(extract_dir, base)
                    with zf.open(info, "r") as src, open(dst, "wb") as out:
                        shutil.copyfileobj(src, out)

                    extracted.append(dst)
        except Exception:
            return False, {}, cleanup_paths, "📑 Не удалось открыть .zip архив базы данных."

        if not extracted:
            return False, {}, cleanup_paths, "📑 В архиве не найдены файлы баз данных."

        local_paths = extracted

    db_paths = [p for p in local_paths if str(p).lower().endswith(".db")]
    wal_paths = [
        p for p in local_paths
        if str(p).lower().endswith(".db-wal") or str(p).lower().endswith(".wal")
    ]

    main_db = ""
    deleted_db = ""
    main_wal = ""

    for p in db_paths:
        kind = _db_upd_sqlite_kind(p)
        if kind == "MAIN" and not main_db:
            main_db = p
        elif kind == "DELETED" and not deleted_db:
            deleted_db = p

    if main_db and wal_paths:
        wanted = main_db + "-wal"
        chosen = ""

        main_base = os.path.basename(main_db).lower()
        main_stem = main_base[:-3] if main_base.endswith(".db") else main_base

        for p in wal_paths:
            low = os.path.basename(p).lower()
            if low in (
                main_base + "-wal",
                main_stem + ".db-wal",
                main_stem + "-wal",
            ):
                chosen = p
                break

        if not chosen:
            chosen = wal_paths[0]

        if chosen != wanted:
            try:
                shutil.copyfile(chosen, wanted)
                chosen = wanted
                cleanup_paths.append(wanted)
            except Exception:
                pass

        if os.path.exists(chosen):
            main_wal = chosen

    if not main_db and not deleted_db:
        return False, {}, cleanup_paths, (
            "📑 Не удалось определить тип базы данных. "
            "Используйте .db или .zip, содержащий основную и/или deleted_labs базу."
        )

    return True, {
        "main_db": main_db,
        "main_wal": main_wal,
        "deleted_db": deleted_db,
    }, cleanup_paths, ""

def _import_sqlite_snapshot_into_deleted_current(snapshot_path: str) -> list[str]:
    init_deleted_db()

    conn2 = sqlite3.connect(DELETED_DB_PATH, check_same_thread=False)
    conn2.row_factory = sqlite3.Row

    imported_tables: list[str] = []
    attached = False

    try:
        try:
            conn2.execute("DETACH DATABASE old_import")
        except Exception:
            pass

        conn2.execute("ATTACH DATABASE ? AS old_import", (snapshot_path,))
        attached = True

        old_tables = [
            r[0]
            for r in conn2.execute(
                "SELECT name FROM old_import.sqlite_master "
                "WHERE type='table' AND name NOT LIKE 'sqlite_%' "
                "ORDER BY name ASC"
            ).fetchall()
        ]

        cur_tables = {
            r[0]
            for r in conn2.execute(
                "SELECT name FROM main.sqlite_master "
                "WHERE type='table' AND name NOT LIKE 'sqlite_%'"
            ).fetchall()
        }

        conn2.execute("BEGIN")

        for table in old_tables:
            if table not in cur_tables:
                continue

            old_cols = [
                r[1]
                for r in conn2.execute(f"PRAGMA old_import.table_info({_q_ident(table)})").fetchall()
            ]
            cur_cols = {
                r[1]
                for r in conn2.execute(f"PRAGMA main.table_info({_q_ident(table)})").fetchall()
            }

            cols = [c for c in old_cols if c in cur_cols]
            if not cols:
                continue

            col_sql = ", ".join(_q_ident(c) for c in cols)

            conn2.execute(
                f"INSERT OR REPLACE INTO main.{_q_ident(table)} ({col_sql}) "
                f"SELECT {col_sql} FROM old_import.{_q_ident(table)}"
            )
            imported_tables.append(str(table))

        conn2.commit()
        return imported_tables

    except Exception:
        try:
            conn2.rollback()
        except Exception:
            pass
        raise

    finally:
        if attached:
            try:
                conn2.execute("DETACH DATABASE old_import")
            except Exception:
                pass
        try:
            conn2.close()
        except Exception:
            pass

def _db_upd_import_main_db(src_db_path: str) -> tuple[bool, str, list[str]]:
    snapshot_path = _db_upd_temp_path("dbupd_main_snapshot", "main.db")
    try:
        _copy_sqlite_db_snapshot(src_db_path, snapshot_path)

        snap_conn = sqlite3.connect(snapshot_path, check_same_thread=False)
        try:
            if not _sqlite_integrity_ok_local(snap_conn):
                return False, "📑 Проверка целостности основной базы данных не пройдена.", []
        finally:
            try:
                snap_conn.close()
            except Exception:
                pass

        imported_tables = _import_sqlite_snapshot_into_current(snapshot_path)

        with DB_LOCK:
            try:
                conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
            except Exception:
                pass

        return True, "", imported_tables

    except Exception as e:
        send_error_report("_db_upd_import_main_db", e)
        return False, "📑 Не удалось импортировать основную базу данных.", []

    finally:
        _db_upd_remove_path(snapshot_path)

def _db_upd_import_deleted_db(src_db_path: str) -> tuple[bool, str, list[str]]:
    snapshot_path = _db_upd_temp_path("dbupd_deleted_snapshot", "deleted.db")
    try:
        _copy_sqlite_db_snapshot(src_db_path, snapshot_path)

        snap_conn = sqlite3.connect(snapshot_path, check_same_thread=False)
        try:
            if not _sqlite_integrity_ok_local(snap_conn):
                return False, "📑 Проверка целостности базы удалённых лабораторий не пройдена.", []
        finally:
            try:
                snap_conn.close()
            except Exception:
                pass

        imported_tables = _import_sqlite_snapshot_into_deleted_current(snapshot_path)
        return True, "", imported_tables

    except Exception as e:
        send_error_report("_db_upd_import_deleted_db", e)
        return False, "📑 Не удалось импортировать базу удалённых лабораторий.", []

    finally:
        _db_upd_remove_path(snapshot_path)

def _db_upd_copy_binary(src_path: str, dst_path: str) -> bool:
    try:
        os.makedirs(os.path.dirname(dst_path), exist_ok=True)
        with open(src_path, "rb") as src, open(dst_path, "wb") as dst:
            shutil.copyfileobj(src, dst)
        return True
    except Exception:
        return False

def _db_upd_refresh_backup_files(main_db: str = "", main_wal: str = "", deleted_db: str = "") -> tuple[bool, str]:
    if main_db:
        if not _sqlite_backup_file(main_db, DB_BACKUP_MAIN_PATH):
            return False, "📑 Не удалось обновить backup основной базы данных."

        if main_wal and os.path.exists(main_wal):
            if not _db_upd_copy_binary(main_wal, DB_BACKUP_MAIN_WAL_PATH):
                return False, "📑 Не удалось обновить backup WAL-файла."
        else:
            _db_upd_remove_path(DB_BACKUP_MAIN_WAL_PATH)

    if deleted_db:
        if not _sqlite_backup_file(deleted_db, DB_BACKUP_DELETED_PATH):
            return False, "📑 Не удалось обновить backup базы удалённых лабораторий."

    return True, ""

def _db_upd_apply_local_files(local_paths: list[str], source_label: str = "") -> tuple[bool, str]:
    ok, bundle, cleanup_paths, err = _db_upd_resolve_local_files(local_paths)
    if not ok:
        for p in cleanup_paths:
            _db_upd_remove_path(p)
        return False, err

    try:
        imported_parts = []

        main_db = str(bundle.get("main_db", "") or "")
        main_wal = str(bundle.get("main_wal", "") or "")
        deleted_db = str(bundle.get("deleted_db", "") or "")

        if main_db:
            ok_main, err_main, tables_main = _db_upd_import_main_db(main_db)
            if not ok_main:
                return False, err_main
            imported_parts.append(
                f"Основная БД: {len(tables_main)} таблиц"
            )

        if deleted_db:
            ok_del, err_del, tables_del = _db_upd_import_deleted_db(deleted_db)
            if not ok_del:
                return False, err_del
            imported_parts.append(
                f"Deleted labs: {len(tables_del)} таблиц"
            )

        if not imported_parts:
            return False, "📑 Не найдено содержимое для импорта."

        ok_backup, err_backup = _db_upd_refresh_backup_files(
            main_db=main_db,
            main_wal=main_wal,
            deleted_db=deleted_db
        )
        if not ok_backup:
            return False, err_backup

        lines = ["✅ Базы данных обновлены."]
        if source_label:
            lines.append(f"Источник: {h(source_label)}")
        lines.extend(imported_parts)

        return True, "\n".join(lines)

    finally:
        for p in cleanup_paths:
            _db_upd_remove_path(p)

def _db_upd_apply_by_db_id(db_id: int) -> tuple[bool, str]:
    row = _db_export_row_by_id(int(db_id))
    if not row:
        return False, "📑 Архив с таким db_id не найден."

    archive_path = (row["archive_path"] or "").strip()
    if not archive_path or not os.path.exists(archive_path):
        return False, "📑 Файл архива для этого db_id больше недоступен."

    title = _db_export_source_title((row["source_kind"] or "").strip())
    return _db_upd_apply_local_files(
        [archive_path],
        source_label=f"db_id {int(db_id)} ({title})"
    )

def _handle_db_fife_upd_command(message, parsed: "Parsed") -> tuple[bool, str]:
    args = (parsed.args or "").strip()

    if args.isdigit():
        return _db_upd_apply_by_db_id(int(args))

    docs = _db_upd_collect_source_documents(message)
    if not docs:
        return False, (
            "📑 Используйте <code>/db_fife_upd</code> одним из способов:\n"
            "1. ответом на сообщение с <code>.db</code> или <code>.zip</code>\n"
            "2. сообщением с прикреплённым документом и caption-командой\n"
            "3. <code>/db_fife_upd &lt;db_id&gt;</code> в личных сообщениях бота"
        )

    local_paths = []
    try:
        for doc in docs:
            file_name = (getattr(doc, "file_name", "") or "").strip()
            low = file_name.lower()

            if not (
                low.endswith(".db")
                or low.endswith(".zip")
                or low.endswith(".db-wal")
                or low.endswith(".wal")
            ):
                continue

            local_paths.append(_db_upd_download_document(doc))

        if not local_paths:
            return False, "📑 Поддерживаются только .db, .db-wal и .zip файлы баз данных."

        return _db_upd_apply_local_files(local_paths, source_label="document upload")

    except Exception as e:
        send_error_report("_handle_db_fife_upd_command", e)
        return False, "📑 Не удалось подготовить файлы для обновления базы данных."

    finally:
        for p in local_paths:
            _db_upd_remove_path(p)

def _send_db_export_archive(chat_id: int, requested_by: int, source_kind: str) -> tuple[bool, str]:
    title = _db_export_source_title(source_kind)

    db_id = 0
    archive_path = ""

    try:
        db_id = _db_export_create_row(str(source_kind or "").strip().upper(), int(requested_by), title)
        if db_id <= 0:
            return False, "📑 Не удалось зарегистрировать архив базы данных."

        ok, archive_path, err = _build_db_export_archive(int(db_id), source_kind)
        if not ok:
            _db_export_delete_row(int(db_id))
            return False, err or "📑 Не удалось подготовить архив базы данных."

        _db_export_update_path(int(db_id), archive_path)

        with open(archive_path, "rb") as f:
            bio = io.BytesIO(f.read())
            bio.name = os.path.basename(archive_path)
            bot.send_document(
                int(chat_id),
                bio,
                caption=f"📦 {title}\n🆔 db_id: <code>{int(db_id)}</code>",
                parse_mode="HTML"
            )

        return True, (
            "✅ Архив базы данных отправлен.\n"
        )

    except Exception as e:
        send_error_report("_send_db_export_archive", e)

        try:
            if archive_path and os.path.exists(archive_path):
                os.remove(archive_path)
        except Exception:
            pass

        if int(db_id) > 0:
            try:
                _db_export_delete_row(int(db_id))
            except Exception:
                pass

        return False, "📑 Не удалось отправить архив базы данных."

def _send_db_files_to_chat(chat_id: int) -> tuple[bool, str]:
    main_copy = ""
    deleted_copy = ""

    try:
        with DB_LOCK:
            try:
                conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
            except Exception:
                pass

        main_copy = _db_snapshot_copy(DB_PATH, "bio_war_snapshot")
        deleted_copy = _db_snapshot_copy(DELETED_DB_PATH, "deleted_labs_snapshot")

        if not main_copy and not deleted_copy:
            return False, "📑 Не удалось подготовить файлы баз данных."

        if main_copy:
            with open(main_copy, "rb") as f:
                bio = io.BytesIO(f.read())
                bio.name = "bio_war.db"
                bot.send_document(int(chat_id), bio, caption="Основная база данных")

        if deleted_copy:
            with open(deleted_copy, "rb") as f:
                bio = io.BytesIO(f.read())
                bio.name = "deleted_labs.db"
                bot.send_document(int(chat_id), bio, caption="База удалённых лабораторий")

        return True, "✅ Файлы баз данных отправлены."
    finally:
        for p in (main_copy, deleted_copy):
            try:
                if p and os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass

def render_db_file_stat_text(owner_id: int) -> str:
    nowv = int(now_ts())

    main_db = _path_size(DB_PATH)
    main_wal = _path_size(DB_PATH + "-wal")
    main_shm = _path_size(DB_PATH + "-shm")
    main_lim = _db_limit_bytes_for_path(DB_PATH)

    del_db = _path_size(DELETED_DB_PATH)

    sch = _db_schedule_row(int(owner_id))
    next_send_ts = int(sch["next_run_ts"] or 0) if sch else 0

    passive_left = max(0, int(DB_CKPT_NEXT_PASSIVE_TS or 0) - nowv)
    truncate_left = max(0, int(DB_CKPT_NEXT_TRUNCATE_TS or 0) - nowv)
    send_left = max(0, next_send_ts - nowv) if next_send_ts > 0 else 0

    lines = []
    lines.append("🧾 Статистика файлов баз данных")
    lines.append("<blockquote expandable>")
    lines.append(f"🗃️ bio_war.db: {_fmt_file_size(main_db)}")
    lines.append(f"🧱 bio_war.db-wal: {_fmt_file_size(main_wal)} / лимит {_fmt_file_size(main_lim)}")
    lines.append(f"📦 bio_war.db-shm: {_fmt_file_size(main_shm)}")
    lines.append(f"🗃️ deleted_labs.db: {_fmt_file_size(del_db)}")
    lines.append("</blockquote>")
    lines.append(f"⏱️ До следующего PASSIVE-чекпоинта: {_format_hms(passive_left)}")
    lines.append(f"⏱️ До следующего TRUNCATE-чекпоинта: {_format_hms(truncate_left)}")

    if next_send_ts > 0:
        lines.append("")
        lines.append(f"⏱️ До следующего автосэйва: {_format_hms(send_left)}")

    return "\n".join(lines)

def _fmt_db_export_source(source_kind: str) -> str:
    kind = str(source_kind or "").strip().upper()
    if kind == "BACKUP":
        return "backup"
    return "main"

def _db_export_rows(limit: int = 200):
    return db_all(
        "SELECT db_id, source_kind, archive_path, requested_by, created_at, request_text "
        "FROM db_file_exports "
        "ORDER BY db_id DESC "
        "LIMIT ?",
        (int(limit),)
    ) or []

def render_db_export_ids_text(owner_id: int) -> str:
    rows = _db_export_rows(200)

    lines = []
    lines.append("🧾 Список известных db_id")

    if not rows:
        lines.append("<blockquote expandable>Список db_id пока пуст.</blockquote>")
        return "\n".join(lines)

    lines.append("<blockquote expandable>")
    for r in rows:
        db_id = int(r["db_id"] or 0)
        source_kind = _fmt_db_export_source(r["source_kind"] or "")
        created_at = int(r["created_at"] or 0)
        dt_txt = time.strftime("%d.%m.%Y %H:%M", time.localtime(created_at)) if created_at > 0 else "—"
        request_text = (r["request_text"] or "").strip()
        if request_text:
            lines.append(
                f"<code>{db_id}</code> | {h(source_kind)} | {h(dt_txt)} | {h(request_text)}"
            )
        else:
            lines.append(
                f"<code>{db_id}</code> | {h(source_kind)} | {h(dt_txt)}"
            )
    lines.append("</blockquote>")
    lines.append("")
    lines.append("💬 Каждый <code>db_id</code> можно скопировать из списка и использовать далее в /db_fife_upd")

    return "\n".join(lines)

def kb_db_export_ids(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(
        _ikb(
            "Состояние db",
            callback_data=_dbstat_cb(int(owner_id), "BACK"),
            style="primary"
        )
    )
    return kb

def _run_db_file_msg_once(now_value: int):
    rows = db_all(
        "SELECT user_id, repeat_spec, next_run_ts, updated_at "
        "FROM db_file_msg_schedule WHERE next_run_ts>0 AND next_run_ts<=?",
        (int(now_value),)
    ) or []

    for row in rows:
        uid = int(row["user_id"])
        spec = {}
        try:
            spec = json.loads((row["repeat_spec"] or "") or "{}")
        except Exception:
            spec = {}

        try:
            _send_db_files_to_chat(int(uid))
        except Exception as e:
            send_error_report("_run_db_file_msg_once", e)

        if spec:
            _db_schedule_reschedule(int(uid), spec, int(row["next_run_ts"] or now_value))

def _parse_its_args(args: str) -> tuple[Optional[int], str]:
    s = (args or "").strip()
    if not s:
        return None, ""

    parts = s.split()
    if len(parts) < 2:
        return None, ""

    token = parts[0].strip()
    mode = parts[1].strip().lower()

    tid = _resolve_or_create_infect_target(token)
    if tid is None:
        return None, ""

    if mode in ("бот", "bot"):
        return int(tid), "bot"
    if mode in ("юзер", "юзер.", "user", "пользователь"):
        return int(tid), "user"

    return int(tid), ""

def _parse_delete_target(message, parsed: "Parsed"):
    target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
    if target_id is not None:
        return int(target_id), target_user_obj

    if message.reply_to_message:
        u = getattr(message.reply_to_message, "from_user", None)
        if u and int(getattr(u, "id", 0) or 0) > 0:
            actor_id = int(getattr(getattr(message, "from_user", None), "id", 0) or 0)
            if int(getattr(u, "id", 0) or 0) != actor_id:
                return int(u.id), u

    tail = (parsed.args or "").strip()
    if tail:
        token = tail.split()[0].strip()
        tid = _resolve_or_create_infect_target(token)
        if tid is not None:
            return int(tid), None

    return None, None

def handle_owner_db_commands(message, parsed: "Parsed"):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    if message.chat.type != "private":
        return

    if not can_manage_support(uid):
        return

    if parsed.cmd == "db_fife":
        bot.reply_to(
            message,
            "📦 Какие файлы баз данных отправить?",
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_db_file_export_choice(int(uid))
        )
        return

    if parsed.cmd == "db_fife_stat":
        bot.reply_to(
            message,
            render_db_file_stat_text(int(uid)),
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_db_file_stat(int(uid))
        )
        return

    if parsed.cmd == "db_fife_msg":
        raw_args = (parsed.args or "").strip()

        if raw_args == "0":
            row = _db_schedule_row(int(uid))
            if not row or int(row["next_run_ts"] or 0) <= 0:
                bot.reply_to(message, "📑 Автосэйв уже выключен.")
                return

            _db_schedule_clear(int(uid))
            bot.reply_to(message, "✅ Автосэйв сброшен.")
            return

        spec, err = _timer_parse_period_spec(raw_args)
        if not spec:
            bot.reply_to(message, err)
            return

        ok, limit_err = _db_schedule_validate_spec(spec)
        if not ok:
            bot.reply_to(message, limit_err)
            return

        _db_schedule_set(int(uid), spec)
        bot.reply_to(
            message,
            f"✅ Автосэйв включен.\n⌛ {_timer_spec_to_text(spec)}",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "db_fife_upd":
        ok, msg = _handle_db_fife_upd_command(message, parsed)
        bot.reply_to(
            message,
            msg,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    target_id, mode = _parse_its_args(parsed.args or "")
    if target_id is None or not mode:
        bot.reply_to(message, "📑 Используйте формат: /its [ссылка/uid/@username] [<code>бот</code>|<code>юзер</code>]", parse_mode="HTML")
        return

    db_exec(
        "INSERT INTO users("
        "user_id, username, first_name, last_name, last_seen, "
        "is_placeholder, is_bot, bot_status_locked"
        ") "
        "VALUES (?,?,?,?,?,?,?,1) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "is_bot=excluded.is_bot, "
        "bot_status_locked=1, "
        "last_seen=excluded.last_seen",
        (int(target_id), None, None, None, int(now_ts()), 0, 1 if mode == "bot" else 0),
        commit=True
    )

    bot.reply_to(
        message,
        f"✅ Статус пользователя <code>{int(target_id)}</code> принудительно установлен как "
        f"<b>{'бот' if mode == 'bot' else 'юзер'}</b>.",
        parse_mode="HTML"
    )

def handle_delete_user_db_command(message, parsed: "Parsed"):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    if not is_support(uid):
        bot.reply_to(message, "📑 Эта команда доступна только агентам техподдержки.")
        return

    target_id, target_user_obj = _parse_delete_target(message, parsed)
    if target_id is None:
        bot.reply_to(message, "📑 Используйте формат: /delete [ссылка/uid/@username] или reply на пользователя/бота.")
        return

    if target_user_obj is not None:
        try:
            capture_user_context(message, target_user_obj)
        except Exception:
            pass

    if int(target_id) == int(uid):
        bot.reply_to(message, "📑 Нельзя удалить из базы данных самого себя.")
        return

    if int(target_id) == int(get_current_creator_id()):
        bot.reply_to(message, "📑 Нельзя удалить из базы данных текущего создателя бота.")
        return

    if is_owner(int(target_id)):
        bot.reply_to(message, "📑 Сначала снимите с этой цели статус старшего агента.")
        return

    if is_agent(int(target_id)):
        bot.reply_to(message, "📑 Сначала снимите с этой цели статус агента техподдержки.")
        return

    shown_tag = _corp_actor_tag(int(target_id))

    try:
        _purge_user_for_delete(int(target_id))
    except Exception as e:
        send_error_report("delete_user_db", e)
        bot.reply_to(message, "📑 Не удалось удалить информацию о пользователе из базы данных.")
        return

    bot.reply_to(
        message,
        f"✅ Информация о цели {shown_tag} удалена из базы данных.",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def get_lab(user_id: int) -> sqlite3.Row:
    ensure_lab_exists(user_id)
    return db_one("SELECT * FROM labs WHERE user_id=?", (int(user_id),))

def set_lab_name(user_id: int, name: Optional[str]):
    db_exec("UPDATE labs SET lab_name=? WHERE user_id=?", (name, int(user_id)), commit=True)

def set_pathogen_name(user_id: int, name: Optional[str]):
    db_exec("UPDATE labs SET pathogen_name=? WHERE user_id=?", (name, int(user_id)), commit=True)

def _normalize_owned_name(name: str) -> str:
    return re.sub(r"\s+", " ", (name or "").strip()).lower()

def is_lab_name_taken(name: str, exclude_user_id: int = 0) -> bool:
    norm = _normalize_owned_name(name)
    if not norm:
        return False

    row = db_one(
        "SELECT user_id FROM labs "
        "WHERE COALESCE(NULLIF(TRIM(lab_name),''), '') <> '' "
        "AND lower(trim(lab_name))=? "
        "AND user_id<>? "
        "LIMIT 1",
        (norm, int(exclude_user_id))
    )
    return row is not None

def is_pathogen_name_taken(name: str, exclude_user_id: int = 0) -> bool:
    norm = _normalize_owned_name(name)
    if not norm:
        return False

    row = db_one(
        "SELECT user_id FROM labs "
        "WHERE COALESCE(NULLIF(TRIM(pathogen_name),''), '') <> '' "
        "AND lower(trim(pathogen_name))=? "
        "AND user_id<>? "
        "LIMIT 1",
        (norm, int(exclude_user_id))
    )
    return row is not None

def get_user_row(user_id: int) -> Optional[sqlite3.Row]:
    return db_one("SELECT * FROM users WHERE user_id=?", (int(user_id),))

def get_notify_prefs(user_id: int) -> tuple[int, int]:
    r = db_one(
        "SELECT COALESCE(notify_chat_id,0) AS c, COALESCE(notify_off,0) AS o FROM users WHERE user_id=?",
        (int(user_id),)
    )
    if not r:
        return 0, 0
    return int(r["c"] or 0), int(r["o"] or 0)

def set_notify_prefs(user_id: int, chat_id: int, off: int):
    db_exec(
        "UPDATE users SET notify_chat_id=?, notify_off=? WHERE user_id=?",
        (int(chat_id), int(off), int(user_id)),
        commit=True
    )

def rp_commands_enabled(user_id: int) -> int:
    r = db_one(
        "SELECT COALESCE(rp_off,0) AS v FROM users WHERE user_id=?",
        (int(user_id),)
    )
    return 0 if (r and int(r["v"] or 0) == 1) else 1

def set_rp_commands_enabled(user_id: int, enabled: int):
    db_exec(
        "UPDATE users SET rp_off=? WHERE user_id=?",
        (0 if int(enabled) == 1 else 1, int(user_id)),
        commit=True
    )

# гендеры
def get_user_gender(user_id: int) -> str:
    row = db_one(
        "SELECT COALESCE(gender,'male') AS g FROM users WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )
    g = str(row["g"] or "male").strip().lower() if row else "male"
    return "female" if g == "female" else "male"

def set_user_gender(user_id: int, gender: str):
    g = "female" if str(gender or "").strip().lower() == "female" else "male"
    db_exec(
        "UPDATE users SET gender=? WHERE user_id=?",
        (g, int(user_id)),
        commit=True
    )

def gender_label(user_id: int) -> str:
    return "♀" if get_user_gender(int(user_id)) == "female" else "♂"

# гендерный словарь
GENDER_TEXTS = {
    # словарь дуэлей
    "duel_hit": {
        "male": "попал",
        "female": "попала",
    },
    "duel_miss": {
        "male": "стреляет, но не попадает",
        "female": "стреляет, но не попадает",
    },
    "duel_aim": {
        "male": "прицеливается получше",
        "female": "прицеливается получше",
    },
    "duel_break_tail": {
        "male": "и сбил прицел",
        "female": "и сбила прицел",
    },
    "duell_break_fail": {
        "male": "попытался сбить прицел",
        "female": "попыталась сбить прицел",
    },
    "duell_break_fail_2": {
        "male": "но не смог",
        "female": "но не смогла",
    },
    "duel_surrender": {
        "male": "сдался",
        "female": "сдалась",
    },
    "duel_cancel": {
        "male": "отменил",
        "female": "отменила",
    },
    "duel_timeout": {
        "male": "проявил",
        "female": "проявила",
    },
    "duel_ready": {
        "male": "принял",
        "female": "приняла",
    },
    "duel_refuse": {
        "male": "отказался",
        "female": "отказалась",
    },
    # словарь ролевых взаимодействий
    "rp_reject": {
        "male": "отклонил",
        "female": "отклонила",
    },
    # словарь заражения
    "infect_exposed": {
        "male": "подверг заражению",
        "female": "подвергла заражению",
    },
    "infect_first_time_target": {
        "male": "Вы ещё не подвергались заражению этим патогеном, поэтому каждый день, пока вы заражены, игрок будет получать по {amount}",
        "female": "Вы ещё не подвергались заражению этим патогеном, поэтому каждый день, пока вы заражены, игрок будет получать по {amount}",
    },
    "infect_first_time_actor": {
        "male": "Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, вы будете получать по {amount}",
        "female": "Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, вы будете получать по {amount}",
    },
    # словарь корпорации
    "corp_inviter_role_owner": {
        "male": "Владелец ",
        "female": "Владелица ",
    },
    "corp_inviter_role_deputy": {
        "male": "Заместитель ",
        "female": "Заместительница ",
    },
    "corp_role_owner_title": {
        "male": "Владелец",
        "female": "Владелица",
    },
    "corp_role_deputy_title": {
        "male": "Заместитель",
        "female": "Заместительница",
    },
    "corp_request_actor_owner_ins": {
        "male": "владельцем",
        "female": "владелицей",
    },
    "corp_request_actor_deputy_ins": {
        "male": "заместителем",
        "female": "заместительницей",
    },
    "corp_request_actor_member_ins": {
        "male": "участником",
        "female": "участницей",
    },
    "corp_invite_chat": {
        "male": "пригласил Вас в Корпорацию",
        "female": "пригласила Вас в Корпорацию",
    },
    "corp_invite_accept": {
        "male": "вступил в Корпорацию",
        "female": "вступила в Корпорацию",
    },
    "corp_invite_reject": {
        "male": "отказался вступать в Корпорацию",
        "female": "отказалась вступать в Корпорацию",
    },
    "corp_invite_notify_accept": {
        "male": "пригласил игрока",
        "female": "пригласила игрока",
    },
    "corp_leave_notify": {
        "male": "покинул Корпорацию",
        "female": "покинула Корпорацию",
    },
    "corp_kick_public": {
        "male": "исключён из корпорации",
        "female": "исключена из корпорации",
    },
    "corp_kick_target": {
        "male": "Вы были исключены из Корпорации",
        "female": "Вы были исключены из Корпорации",
    },
    "corp_deputy_assign": {
        "male": "назначен заместителем Корпорации",
        "female": "назначена заместительницей Корпорации",
    },
    "corp_deputy_remove": {
        "male": "больше не является заместителем Корпорации",
        "female": "больше не является заместительницей Корпорации",
    },
}

def _gender_pick(user_id: int, key: str, **fmt) -> str:
    g = get_user_gender(int(user_id))
    bucket = GENDER_TEXTS.get(str(key), {}) or {}
    text = str(bucket.get("female" if g == "female" else "male", "") or "")
    if not text:
        text = str(bucket.get("male", "") or "")
    if fmt:
        try:
            text = text.format(**fmt)
        except Exception:
            pass
    return text

# логика уведомлениий
def get_pm_opened(user_id: int) -> int:
    r = db_one(
        "SELECT COALESCE(pm_opened,0) AS p FROM users WHERE user_id=?",
        (int(user_id),)
    )
    return int(r["p"] or 0) if r else 0

def set_pm_opened(user_id: int, value: int = 1):
    db_exec(
        "UPDATE users SET pm_opened=? WHERE user_id=?",
        (int(value), int(user_id)),
        commit=True
    )

def _known_common_chat_ids_for_user(user_id: int) -> list[int]:
    rows = db_all(
        "SELECT DISTINCT cm.chat_id "
        "FROM chat_members cm "
        "LEFT JOIN bot_group_chats bg ON bg.chat_id=cm.chat_id "
        "WHERE cm.user_id=? "
        "  AND (bg.chat_id IS NULL OR COALESCE(bg.is_active,0)=1) "
        "ORDER BY cm.chat_id ASC",
        (int(user_id),)
    ) or []
    return [int(r["chat_id"]) for r in rows]

def _pick_random_common_chat_for_user(user_id: int) -> int:
    chats = _known_common_chat_ids_for_user(int(user_id))
    if not chats:
        return 0
    cid = int(random.choice(chats))
    set_notify_prefs(int(user_id), cid, 0)
    return cid

def send_user_notification(user_id: int, text: str, *, respect_notify_off: bool = True):
    """
    Отправляет уведомление пользователю по правилам:
    - если уведомления отключены -> None
    - если выбран чат -> туда
    - если выбранного чата нет:
        * если ЛС уже открывались -> в ЛС
        * иначе -> в случайный общий чат и запоминаем его
    Если ничего не удалось — молча None.
    """
    uid = int(user_id)

    try:
        notify_chat_id, notify_off = get_notify_prefs(uid)
        if respect_notify_off and int(notify_off) == 1 and int(notify_chat_id) == 0:
            return None

        pm_opened = get_pm_opened(uid)
        if int(notify_chat_id) != 0:
            dest = int(notify_chat_id)
        else:
            dest = int(uid) if int(pm_opened) == 1 else int(_pick_random_common_chat_for_user(uid) or 0)

        if dest == 0:
            return None

        try:
            return bot.send_message(dest, text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            if int(notify_chat_id) != 0:
                try:
                    set_notify_prefs(uid, 0, 0)
                except Exception:
                    pass

            if int(pm_opened) == 1:
                try:
                    return bot.send_message(uid, text, parse_mode="HTML", disable_web_page_preview=True)
                except Exception:
                    return None

            alt = _pick_random_common_chat_for_user(uid)
            if alt != 0 and alt != dest:
                try:
                    return bot.send_message(int(alt), text, parse_mode="HTML", disable_web_page_preview=True)
                except Exception:
                    return None

            return None
    except Exception:
        return None

_CHAT_TITLE_CACHE: Dict[int, tuple[str, int]] = {}
_CHAT_TITLE_CACHE_TTL = 600

def corp_notify_enabled(user_id: int) -> int:
    r = db_one("SELECT COALESCE(enabled,1) AS e FROM corp_notify_prefs WHERE user_id=? LIMIT 1", (int(user_id),))
    if not r:
        return 1
    return int(r["e"] or 0)

def set_corp_notify_enabled(user_id: int, enabled: int):
    db_exec(
        "INSERT INTO corp_notify_prefs(user_id, enabled) VALUES (?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET enabled=excluded.enabled",
        (int(user_id), int(enabled)),
        commit=True
    )

def _user_corp_role_soft(user_id: int) -> tuple[int, str, str]:
    r = db_one(
        "SELECT c.corp_id, c.name, m.role "
        "FROM corp_members m "
        "JOIN corps c ON c.corp_id=m.corp_id "
        "WHERE m.user_id=? "
        "ORDER BY CASE m.role "
        "           WHEN 'owner' THEN 0 "
        "           WHEN 'deputy' THEN 1 "
        "           ELSE 2 "
        "         END, m.joined_at ASC "
        "LIMIT 1",
        (int(user_id),)
    )
    if not r:
        return 0, "", ""
    return int(r["corp_id"] or 0), (r["name"] or "").strip(), (r["role"] or "").strip()

def _get_chat_title_cached(chat_id: int) -> str:
    cid = int(chat_id)
    now = now_ts()

    cached = _CHAT_TITLE_CACHE.get(cid)
    if cached and (now - int(cached[1])) < _CHAT_TITLE_CACHE_TTL:
        return cached[0]

    title = f"чат {cid}"
    try:
        ch = bot.get_chat(cid)
        title = (
            getattr(ch, "title", None)
            or getattr(ch, "full_name", None)
            or getattr(ch, "first_name", None)
            or f"чат {cid}"
        )
    except Exception:
        pass

    _CHAT_TITLE_CACHE[cid] = (str(title), int(now))
    return str(title)

def _format_settings_left(seconds: int) -> str:
    sec = max(0, int(seconds))
    d = sec // 86400
    h = (sec % 86400) // 3600
    m = (sec % 3600) // 60

    parts = []
    if d > 0:
        parts.append(f"{d} {_ru_form(d, 'день', 'дня', 'дней')}")
    if h > 0:
        parts.append(f"{h} {_ru_form(h, 'час', 'часа', 'часов')}")
    if not parts:
        mm = max(1, m)
        parts.append(f"{mm} {_ru_form(mm, 'минута', 'минуты', 'минут')}")
    return " ".join(parts[:2])

def _settings_restore_timer_text(user_id: int) -> str:
    row = get_deleted_lab_row(int(user_id))
    if not row:
        return "❌"

    now = now_ts()
    deleted_at = int(row["deleted_at"] or 0)
    purge_at = int(row["purge_at"] or 0)
    self_until = int(deleted_at + 3 * 86400)

    if now <= self_until:
        return f"до самовосстановления: {_format_settings_left(self_until - now)}"
    if now <= purge_at:
        return f"через поддержку: {_format_settings_left(purge_at - now)}"
    return "❌"

def _settings_cb(uid: int, act: str) -> str:
    return f"{SETUI_TAG}:{int(uid)}:{act}"

def _settings_parse_cb(data: str):
    try:
        p = (data or "").split(":")
        if len(p) != 3 or p[0] != SETUI_TAG:
            return None, None
        return int(p[1]), (p[2] or "").strip().upper()
    except Exception:
        return None, None

def corp_notice_manager_ids(corp_id: int) -> list[int]:
    out = []
    for uid in corp_manager_ids(int(corp_id)):
        if corp_notify_enabled(int(uid)) == 1:
            out.append(int(uid))
    return out

def render_settings_text(user_id: int, current_chat_id: int = 0) -> str:
    uid = int(user_id)
    current_chat_id = int(current_chat_id or 0)

    lab_row = db_one(
        "SELECT COALESCE(hide_balance,0) AS hb, COALESCE(hide_lab,0) AS hl, COALESCE(lab_active,0) AS la "
        "FROM labs WHERE user_id=? LIMIT 1",
        (uid,)
    )
    has_active_lab = bool(lab_row) and int(lab_row["la"] or 0) == 1

    if has_active_lab:
        hb = int(lab_row["hb"] or 0)
        hl = int(lab_row["hl"] or 0)
        bal_txt = "🔒" if hb == 1 else "🔓"
        lab_txt = "🔒" if hl == 1 else "🔓"
    else:
        bal_txt = "❌"
        lab_txt = "❌"

    notify_chat_id, notify_off = get_notify_prefs(uid)
    if int(notify_off) == 1 and int(notify_chat_id) == 0:
        notify_txt = "🔇"
    elif int(notify_chat_id) != 0:
        notify_txt = f"{h(_get_chat_title_cached(int(notify_chat_id)))} 🔊"
    else:
        notify_txt = "личные сообщения 🔊"

    deleted_row = get_deleted_lab_row(uid)
    cid, _cname, role = _user_corp_role_soft(uid)

    title = "⚙️ Параметры"
    if current_chat_id < 0:
        row = get_user_row(uid)
        chat_name = get_chat_user_name(int(current_chat_id), int(uid))
    
        if row:
            shown_name = chat_name or standard_display_name(
                row["first_name"] or "",
                row["last_name"] or "",
                row["username"] or "",
                int(uid)
            )
            shown_tag = tg_mention(
                int(uid),
                shown_name,
                username=(row["username"] or "")
            )
        else:
            shown_name = chat_name or str(int(uid))
            shown_tag = tg_mention(int(uid), shown_name)
    
        title = f"⚙️ Параметры <b>«{shown_tag}»</b>"

    lines = []
    lines.append(title)
    lines.append("")
    lines.append("ПРИВАТНЫЕ НАСТРОЙКИ:")
    lines.append(f"👤 Пол: {gender_label(uid)}")
    lines.append(f"💰 Баланс: {bal_txt}")
    lines.append(f"🔬 Досье лаборатории: {lab_txt}")
    lines.append(f"🗨️ РП-команды: {'⭕' if rp_commands_enabled(uid) == 1 else '❌'}")
    lines.append("")
    lines.append("УВЕДОМЛЕНИЯ:")
    lines.append(f"Уведомления: {notify_txt}")

    if int(cid) > 0:
        corp_notify_txt = "🔊" if corp_notify_enabled(uid) == 1 else "🔇"
        lines.append(f"Корпоративные уведомления: {corp_notify_txt}")

    if deleted_row:
        lines.append(f"⏳ Таймер удаления лабы {_settings_restore_timer_text(uid)}")

    return "\n".join(lines)

def kb_settings(
        user_id: int,
        current_chat_id: int = 0, 
        current_chat_type: str = "private"
) -> InlineKeyboardMarkup:
    uid = int(user_id)
    kb = InlineKeyboardMarkup(row_width=2)

    lab_row = db_one(
        "SELECT COALESCE(hide_balance,0) AS hb, COALESCE(hide_lab,0) AS hl, COALESCE(lab_active,0) AS la "
        "FROM labs WHERE user_id=? LIMIT 1",
        (uid,)
    )
    has_active_lab = bool(lab_row) and int(lab_row["la"] or 0) == 1

    if has_active_lab:
        hb = int(lab_row["hb"] or 0)
        hl = int(lab_row["hl"] or 0)

        kb.row(
            _ikb(
                "Открыть баланс" if hb == 1 else "Скрыть баланс",
                callback_data=_settings_cb(uid, "HB"),
                style=("success" if hb == 1 else "danger")
            ),
            _ikb(
                "Открыть досье" if hl == 1 else "Скрыть досье",
                callback_data=_settings_cb(uid, "HL"),
                style=("success" if hl == 1 else "danger")
            )
        )

    g = get_user_gender(uid)
    rp_en = rp_commands_enabled(uid)
    
    kb.row(
        _ikb(
            f"Пол: {'Мужской' if g == 'male' else 'Женский'}",
            callback_data=_settings_cb(uid, "G"),
            style="primary"
        ),
        _ikb(
            "Выключить РП" if rp_en == 1 else "Включить РП",
            callback_data=_settings_cb(uid, "RP"),
            style=("danger" if rp_en == 1 else "success")
        )
    )

    notify_chat_id, notify_off = get_notify_prefs(uid)
    can_show_chat_notify = (
        str(current_chat_type or "").lower() in ("group", "supergroup")
        and int(current_chat_id) != 0
        and (int(notify_chat_id) != int(current_chat_id) or int(notify_off) == 1)
    )

    if int(notify_off) == 1 and int(notify_chat_id) == 0:
        if can_show_chat_notify:
            kb.row(
                _ikb("Уведомления в этот чат", callback_data=_settings_cb(uid, "NCHAT"), style="primary"),
                _ikb("Включить уведомления в ЛС", callback_data=_settings_cb(uid, "NPM"), style="success")
            )
        else:
            kb.add(_ikb("Включить уведомления в ЛС", callback_data=_settings_cb(uid, "NPM"), style="success"))

    elif int(notify_chat_id) == 0:
        if can_show_chat_notify:
            kb.row(
                _ikb("Уведомления в этот чат", callback_data=_settings_cb(uid, "NCHAT"), style="primary"),
                _ikb("Отключить уведомления", callback_data=_settings_cb(uid, "NOFF"), style="danger")
            )
        else:
            kb.add(_ikb("Отключить уведомления", callback_data=_settings_cb(uid, "NOFF"), style="danger"))

    else:
        kb.row(
            _ikb("Уведомления в ЛС", callback_data=_settings_cb(uid, "NPM"), style="primary"),
            _ikb("Отключить уведомления", callback_data=_settings_cb(uid, "NOFF"), style="danger")
        )

        if can_show_chat_notify:
            kb.add(_ikb("Уведомления в этот чат", callback_data=_settings_cb(uid, "NCHAT"), style="primary"))

    _cid, _cname, role = _user_corp_role_soft(uid)
    if int(_cid) > 0:
        en = corp_notify_enabled(uid)
        kb.add(
            _ikb(
                "Выключить корп. уведомления" if en == 1 else "Включить корп. уведомления",
                callback_data=_settings_cb(uid, "CN"),
                style=("danger" if en == 1 else "success")
            )
        )

    return kb

def handle_settings_command(message):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    bot.reply_to(
        message,
        render_settings_text(uid, int(message.chat.id)),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_settings(uid, int(message.chat.id), str(message.chat.type or "private"))
    )

def report_set_state(user_id: int, category: str, stage: str):
    db_exec(
        "INSERT INTO report_state(user_id, category, stage, created_ts) VALUES (?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET category=excluded.category, stage=excluded.stage, created_ts=excluded.created_ts",
        (int(user_id), str(category or ""), str(stage or ""), int(now_ts())),
        commit=True
    )

def report_get_state(user_id: int) -> tuple[str, str]:
    r = db_one("SELECT stage, category FROM report_state WHERE user_id=? LIMIT 1", (int(user_id),))
    if not r:
        return "", ""
    return (str(r["stage"] or ""), str(r["category"] or ""))

def report_clear_state(user_id: int):
    db_exec("DELETE FROM report_state WHERE user_id=?", (int(user_id),), commit=True)

# report
def _report_cb(uid: int, act: str) -> str:
    return f"{REPORTUI_TAG}:{int(uid)}:{str(act).upper()}"

def _report_parse_cb(data: str):
    try:
        p = (data or "").split(":")
        if len(p) != 3 or p[0] != REPORTUI_TAG:
            return None, None
        return int(p[1]), str(p[2] or "").upper()
    except Exception:
        return None, None

def _report_is_test_user(user_id: int) -> bool:
    uid = int(user_id)
    return is_creator(uid) or is_owner(uid) or is_agent(uid)

def _report_test_prefix_html() -> str:
    return "<b>⚠️ Это тестовое сообщение</b>"

def _report_text_for_user(user_id: int, text: str) -> str:
    body = str(text or "").strip()
    if _report_is_test_user(int(user_id)):
        if body:
            return f"{_report_test_prefix_html()}\n{body}"
        return _report_test_prefix_html()
    return body

def kb_report_menu(uid: int, *, appeal_only: bool = False) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)

    if appeal_only:
        kb.add(_ikb("Апелляция", callback_data=_report_cb(int(uid), "APPEAL"), style="primary"))
        return kb

    kb.add(_ikb("Восстановление лаборатории", callback_data=_report_cb(int(uid), "RESTORE"), style="primary"))
    kb.row(
        _ikb("Ошибка бота", callback_data=_report_cb(int(uid), "BUG"), style="primary"),
        _ikb("Жалоба на пользователя", callback_data=_report_cb(int(uid), "USER"), style="danger"),
    )
    kb.row(
        _ikb("Апелляция", callback_data=_report_cb(int(uid), "APPEAL")),
        _ikb("Другое", callback_data=_report_cb(int(uid), "OTHER")),
    )
    return kb

def _report_prompt(uid: int, cat: str) -> str:
    cat = str(cat or "").upper()

    if cat == "USER":
        text = (
            "Отправьте одним сообщением:\n"
            "・ 1-я строка @username нарушителя\n"
            "・ со 2-й строки описание проблемы\n\n"
            "Можно прикрепить фото или видео к этому сообщению."
        )
        return _report_text_for_user(int(uid), text)

    if cat == "RESTORE":
        row = get_deleted_lab_row(int(uid))
        extra = ""
        if row:
            deleted_at = int(row["deleted_at"] or 0)
            purge_at = int(row["purge_at"] or 0)
            extra = (
                f"\n\n🧾 Лаборатория удалена: <code>{h(_fmt_ts(deleted_at))}</code>\n"
                f"🧾 Крайний срок восстановления через поддержку: <code>{h(_fmt_ts(purge_at))}</code>"
            )
        text = (
            "Опишите Ваш запрос на восстановление лаборатории одним сообщением.\n"
            "Можно приложить фото или видео.\n"
            "Подробнее опишите причину."
            f"{extra}"
        )
        return _report_text_for_user(int(uid), text)

    if cat == "APPEAL":
        text = (
            "Отправьте описание апелляции одним сообщением.\n\n"
            "Можно прикрепить фото или видео к этому сообщению."
        )
        return _report_text_for_user(int(uid), text)

    text = (
        "Отправьте описание проблемы одним сообщением.\n\n"
        "Можно прикрепить фото или видео к этому сообщению."
    )
    return _report_text_for_user(int(uid), text)

def _send_report_to_service_team(admin_text: str, media_type: str = "", media_file_id: str = "") -> bool:
    try:
        if media_type and media_file_id:
            if len(admin_text) <= 900:
                return _send_media_to_report_recipients(
                    media_type,
                    media_file_id,
                    caption=admin_text,
                    parse_mode="HTML"
                )

            ok_text = _send_message_to_report_recipients(
                admin_text,
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            ok_media = _send_media_to_report_recipients(media_type, media_file_id)
            return bool(ok_text or ok_media)

        return _send_message_to_report_recipients(
            admin_text,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    except Exception:
        return False

def _handle_report_content_message(message) -> bool:
    uid = int(message.from_user.id)
    stage, cat = report_get_state(uid)
    if message.chat.type != "private" or stage != "await_content" or not cat:
        return False

    raw = ""
    if message.content_type == "text":
        raw = (message.text or "").strip()
    else:
        raw = (message.caption or "").strip()

    if raw.startswith("/"):
        return False

    if not raw:
        bot.reply_to(
            message,
            _report_text_for_user(uid, "Пустое сообщение. Пришлите текст описания, при желании добавив фото или видео."),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return True

    target_un = ""
    desc = ""

    cat_u = str(cat).upper()

    if is_bot_banned(int(uid)) and cat_u != "APPEAL":
        report_clear_state(int(uid))
        bot.reply_to(
            message,
            _report_text_for_user(uid, "Для заблокированных пользователей доступна только апелляция."),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return True

    if cat_u == "USER":
        lines = raw.splitlines()
        if not lines or not lines[0].strip().startswith("@"):
            bot.reply_to(
                message,
                _report_text_for_user(
                    uid,
                    "Для жалобы на пользователя укажите сообщение в формате:\n"
                    "1-я строка — @username нарушителя\n"
                    "со 2-й строки — описание проблемы."
                ),
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return True

        target_un = lines[0].strip()
        desc = "\n".join(lines[1:]).strip()
        if not desc:
            bot.reply_to(
                message,
                _report_text_for_user(uid, "Добавьте описание проблемы со второй строки."),
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return True
    else:
        desc = raw.strip()

    from_name = user_full_name(message.from_user)
    from_un = (getattr(message.from_user, "username", None) or "").strip()
    from_line = h(from_name) + (f" (@{h(from_un)})" if from_un else "")
    ts_txt = _fmt_ts(now_ts())
    cat_title = REPORT_CATS.get(cat_u, cat_u)

    admin_text = f"Репорт {h(ts_txt)}\nОт {from_line}\nКатегория: {h(cat_title)}\n"

    if cat_u == "USER":
        admin_text += f"На {h(target_un)}\n"

    if cat_u == "RESTORE":
        row = get_deleted_lab_row(uid)
        if row:
            deleted_at = int(row["deleted_at"] or 0)
            purge_at = int(row["purge_at"] or 0)
            admin_text += f"Удалена: <code>{h(_fmt_ts(deleted_at))}</code>\n"
            admin_text += f"Support restore до: <code>{h(_fmt_ts(purge_at))}</code>\n"
        else:
            admin_text += "Сохранённая лаборатория для восстановления не найдена.\n"

    admin_text += "Описание проблемы:\n"
    admin_text += f"<i>{h(desc)}</i>"

    if _report_is_test_user(uid):
        admin_text = f"{_report_test_prefix_html()}\n{admin_text}"

    media_type = ""
    media_file_id = ""
    try:
        if message.content_type == "photo" and message.photo:
            media_type = "photo"
            media_file_id = message.photo[-1].file_id
        elif message.content_type == "video" and message.video:
            media_type = "video"
            media_file_id = message.video.file_id
    except Exception:
        media_type = ""
        media_file_id = ""

    ok = _send_report_to_service_team(admin_text, media_type=media_type, media_file_id=media_file_id)
    if not ok:
        bot.reply_to(
            message,
            _report_text_for_user(uid, "Не удалось отправить репорт. Попробуйте позже."),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return True

    report_clear_state(uid)

    if cat_u == "RESTORE":
        bot.reply_to(
            message,
            _report_text_for_user(uid, "Запрос на восстановление лаборатории отправлен тех.поддержке на рассмотрение."),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    else:
        bot.reply_to(
            message,
            _report_text_for_user(uid, "Репорт отправлен тех.поддержке на рассмотрение. Благодарим вас за поддержку проекта."),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    return True

def handle_report_command(message):
    if message.chat.type != "private":
        bot.reply_to(
            message,
            "📑 Эта команда работает только в личных сообщениях бота.",
            reply_markup=kb_open_bot_pm()
        )
        return

    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    report_clear_state(uid)

    appeal_only = is_bot_banned(int(uid))

    bot.reply_to(
        message,
        _report_text_for_user(uid, "Выберите категорию запроса:"),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_report_menu(uid, appeal_only=appeal_only)
    )

# balans chains
def _balance_chain_row(user_id: int):
    return db_one(
        "SELECT user_id, chain_kind, button_text, payload_json, source_chat_id, source_message_id, updated_at "
        "FROM balance_chain_state WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )

def get_balance_chain_state(user_id: int) -> Optional[dict]:
    row = _balance_chain_row(int(user_id))
    if not row:
        return None

    try:
        payload = json.loads((row["payload_json"] or "") or "{}")
        if not isinstance(payload, dict):
            payload = {}
    except Exception:
        payload = {}

    return {
        "user_id": int(row["user_id"]),
        "chain_kind": str(row["chain_kind"] or "").strip(),
        "button_text": str(row["button_text"] or "").strip(),
        "payload": payload,
        "source_chat_id": int(row["source_chat_id"] or 0),
        "source_message_id": int(row["source_message_id"] or 0),
        "updated_at": int(row["updated_at"] or 0),
    }

def clear_balance_chain_state(user_id: int):
    db_exec(
        "DELETE FROM balance_chain_state WHERE user_id=?",
        (int(user_id),),
        commit=True
    )

def set_balance_chain_state(
    user_id: int,
    chain_kind: str,
    button_text: str,
    payload: Optional[dict] = None,
    *,
    source_chat_id: int = 0,
    source_message_id: int = 0
):
    data = payload if isinstance(payload, dict) else {}
    db_exec(
        "INSERT INTO balance_chain_state("
        "user_id, chain_kind, button_text, payload_json, source_chat_id, source_message_id, updated_at"
        ") VALUES (?,?,?,?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "chain_kind=excluded.chain_kind, "
        "button_text=excluded.button_text, "
        "payload_json=excluded.payload_json, "
        "source_chat_id=excluded.source_chat_id, "
        "source_message_id=excluded.source_message_id, "
        "updated_at=excluded.updated_at",
        (
            int(user_id),
            str(chain_kind or "").strip(),
            str(button_text or "").strip(),
            json.dumps(data, ensure_ascii=False),
            int(source_chat_id or 0),
            int(source_message_id or 0),
            int(now_ts()),
        ),
        commit=True
    )

def set_balance_chain_state_from_message(
    message,
    chain_kind: str,
    button_text: str,
    payload: Optional[dict] = None
):
    uid = int(getattr(getattr(message, "from_user", None), "id", 0) or 0)
    if uid <= 0:
        return

    set_balance_chain_state(
        int(uid),
        str(chain_kind or "").strip(),
        str(button_text or "").strip(),
        payload if isinstance(payload, dict) else {},
        source_chat_id=int(getattr(getattr(message, "chat", None), "id", 0) or 0),
        source_message_id=int(getattr(message, "message_id", 0) or 0),
    )

def get_balance_chain_button_text(user_id: int) -> str:
    state = get_balance_chain_state(int(user_id))
    if not state:
        return ""
    return str(state.get("button_text") or "").strip()

# chat member
def remember_chat_member(chat_id: int, tg_user):
    upsert_user(tg_user)

    try:
        _merge_placeholder_to_real_user(tg_user)
    except Exception:
        pass

    if bool(getattr(tg_user, "is_bot", False)):
        try:
            db_exec(
                "UPDATE users "
                "SET is_bot=CASE "
                "    WHEN COALESCE(bot_status_locked,0)=1 THEN is_bot "
                "    ELSE 1 "
                "END, "
                "is_placeholder=0 "
                "WHERE user_id=?",
                (int(tg_user.id),),
                commit=True
            )
        except Exception:
            pass

    uname = (getattr(tg_user, "username", None) or "").strip().lower() or None
    db_exec(
        "INSERT INTO chat_members(chat_id,user_id,username,last_seen) VALUES(?,?,?,?) "
        "ON CONFLICT(chat_id,user_id) DO UPDATE SET username=excluded.username, last_seen=excluded.last_seen",
        (int(chat_id), int(tg_user.id), uname, now_ts()),
        commit=True
    )

def remember_bot_group_chat(chat_id: int, title: str = "", chat_type: str = "group", is_active: int = 1, owner_id: int = 0):
    db_exec(
        "INSERT INTO bot_group_chats(chat_id, title, chat_type, is_active, updated_at, owner_id) VALUES (?,?,?,?,?,?) "
        "ON CONFLICT(chat_id) DO UPDATE SET "
        "title=excluded.title, chat_type=excluded.chat_type, is_active=excluded.is_active, updated_at=excluded.updated_at, "
        "owner_id=CASE WHEN excluded.owner_id>0 THEN excluded.owner_id ELSE bot_group_chats.owner_id END",
        (
            int(chat_id),
            str(title or ""),
            str(chat_type or ""),
            int(is_active),
            int(now_ts()),
            int(owner_id or 0)
        ),
        commit=True
    )

def _users_total_count() -> int:
    row = db_one("SELECT COUNT(*) AS c FROM users WHERE COALESCE(is_bot,0)=0")
    return int(row["c"] or 0) if row else 0

def _users_bot_count() -> int:
    row = db_one("SELECT COUNT(*) AS c FROM users WHERE COALESCE(is_bot,0)=1")
    return int(row["c"] or 0) if row else 0

def _bot_group_chat_count() -> int:
    row = db_one(
        "SELECT COUNT(DISTINCT chat_id) AS c FROM ("
        "  SELECT chat_id FROM bot_group_chats WHERE COALESCE(is_active,0)=1 "
        "  UNION "
        "  SELECT chat_id FROM chat_members "
        ") t"
    )
    return int(row["c"] or 0) if row else 0

def sync_chat_admins(chat_id: int):
    """
    Пытается получить всех админов чата и записать их в chat_members.
    Заодно фиксирует владельца чата в bot_group_chats.owner_id.
    """
    try:
        admins = bot.get_chat_administrators(int(chat_id)) or []
    except Exception:
        return

    owner_id = 0

    for cm in admins:
        try:
            u = getattr(cm, "user", None)
            st = (getattr(cm, "status", "") or "").lower()
            if u:
                remember_chat_member(int(chat_id), u)
                if st == "creator":
                    owner_id = int(u.id)
        except Exception:
            pass

    if owner_id > 0:
        db_exec(
            "UPDATE bot_group_chats SET owner_id=?, updated_at=? WHERE chat_id=?",
            (int(owner_id), int(now_ts()), int(chat_id)),
            commit=True
        )

def _known_chat_member_count(chat_id: int, exclude_user_id: int = 0) -> int:
    row = db_one(
        "SELECT COUNT(*) AS c "
        "FROM chat_members "
        "WHERE chat_id=? AND user_id>0 AND user_id<>?",
        (int(chat_id), int(exclude_user_id))
    )
    return int(row["c"] or 0) if row else 0

def capture_user_context(message, tg_user):
    """
    Универсально: фиксируем пользователя в users,
    а в группе ещё и в chat_members (чтобы команды по @username работали).
    """
    try:
        if message.chat.type in ("group", "supergroup"):
            remember_chat_member(message.chat.id, tg_user)
        else:
            upsert_user(tg_user)
    except Exception:
        pass

def _collect_target_tokens_from_text(text: str) -> list[str]:
    s = str(text or "")
    out: list[str] = []
    seen = set()

    def _add(tok: str):
        tok = (tok or "").strip()
        if tok and tok not in seen:
            seen.add(tok)
            out.append(tok)

    pure = s.strip()
    if pure:
        _add(pure)

    for m in re.finditer(r"tg://openmessage\?user_id=\d+", s, flags=re.IGNORECASE):
        _add(m.group(0))

    for m in re.finditer(r"tg://user\?id=\d+", s, flags=re.IGNORECASE):
        _add(m.group(0))

    for m in re.finditer(r"(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z0-9_]{3,64})/?", s, flags=re.IGNORECASE):
        _add("@" + m.group(1))

    for m in re.finditer(r"(?<![\w/])@([A-Za-z0-9_]{3,64})", s):
        _add("@" + m.group(1))

    for m in re.finditer(r"(?<!\d)(-?\d{1,20})(?!\d)", s):
        _add(m.group(1))

    return out

def _resolve_single_target_from_text(text: str, resolver) -> Optional[int]:
    resolved: list[int] = []
    seen_ids = set()

    for tok in _collect_target_tokens_from_text(text):
        try:
            tid = resolver(tok)
        except Exception:
            tid = None

        if tid is None:
            continue

        tid = int(tid)
        if tid not in seen_ids:
            seen_ids.add(tid)
            resolved.append(tid)

    if len(resolved) == 1:
        return int(resolved[0])

    return None

def _reply_message_text_and_entities(rm):
    raw = (getattr(rm, "text", None) or getattr(rm, "caption", None) or "")
    ents = []
    try:
        ents.extend(list(getattr(rm, "entities", None) or []))
    except Exception:
        pass
    try:
        ents.extend(list(getattr(rm, "caption_entities", None) or []))
    except Exception:
        pass
    return raw, ents

def _entity_slice_text(raw: str, ent) -> str:
    try:
        off = int(getattr(ent, "offset", 0) or 0)
        ln = int(getattr(ent, "length", 0) or 0)
        if ln <= 0:
            return ""
        return str(raw or "")[off:off + ln]
    except Exception:
        return ""

def _collect_reply_target_ids(message, *, exclude_user_ids=None) -> list[int]:
    rm = getattr(message, "reply_to_message", None)
    if not rm:
        return []

    exclude = {int(x) for x in (exclude_user_ids or []) if int(x or 0) != 0}
    raw, ents = _reply_message_text_and_entities(rm)

    out: list[int] = []
    seen = set()

    def _add(uid: Optional[int]):
        if uid is None:
            return
        uid = int(uid)
        if uid in exclude or uid in seen:
            return
        seen.add(uid)
        out.append(uid)

    for e in ents:
        et = (getattr(e, "type", "") or "").strip().lower()

        if et == "text_mention":
            u = getattr(e, "user", None)
            if u and getattr(u, "id", None):
                try:
                    capture_user_context(message, u)
                except Exception:
                    pass
                _add(int(u.id))
            continue

        token = ""
        if et == "text_link":
            token = (getattr(e, "url", "") or "").strip()
        elif et == "url":
            token = _entity_slice_text(raw, e).strip()
        elif et == "mention":
            token = _entity_slice_text(raw, e).strip()

        if token:
            try:
                tid = _strict_single_target_token(token)
            except Exception:
                tid = None
            _add(tid)

    for tok in _collect_target_tokens_from_text(raw):
        try:
            tid = _strict_single_target_token(tok)
        except Exception:
            tid = None
        _add(tid)

    return out

def _pick_reply_target_id(message, *, exclude_user_ids=None) -> Optional[int]:
    ids = _collect_reply_target_ids(message, exclude_user_ids=exclude_user_ids)
    if not ids:
        return None
    if len(ids) == 1:
        return int(ids[0])
    return int(random.choice(ids))

def resolve_target_from_reply_or_args(message, parsed: Optional["Parsed"]):
    """
    Возвращает (target_id, target_user_obj_or_None).

    При reply:
      1) если reply на не-бота и команду использует НЕ автор replied-сообщения —
         всегда берём автора replied-сообщения;
      2) иначе, если в replied-сообщении есть ссылки/упоминания пользователей —
         берём цель из них, исключая самого вызывающего команду;
         если после исключения остаётся несколько целей — берём случайную.
      3) если целей в тексте нет — fallback на автора replied-сообщения,
         но только если это не бот и не сам вызывающий.
    При args — поддерживает один целевой uid, @username или ссылку даже внутри текста args.
    """
    actor_id = int(getattr(getattr(message, "from_user", None), "id", 0) or 0)

    if message.reply_to_message:
        u = getattr(message.reply_to_message, "from_user", None)

        if (
            u
            and not bool(getattr(u, "is_bot", False))
            and int(getattr(u, "id", 0) or 0) != actor_id
        ):
            capture_user_context(message, u)
            return int(u.id), u

        tid = _pick_reply_target_id(message, exclude_user_ids={actor_id})
        if tid is not None:
            return int(tid), None

        if (
            u
            and not bool(getattr(u, "is_bot", False))
            and int(getattr(u, "id", 0) or 0) == actor_id
        ):
            capture_user_context(message, u)
            return int(u.id), u

    if parsed and parsed.args:
        tid = _resolve_single_target_from_text((parsed.args or "").strip(), _strict_single_target_token)
        if tid is not None:
            return int(tid), None

    return None, None

def _is_game_bot_target(target_id: int, target_user_obj=None) -> bool:
    try:
        if target_user_obj is not None:
            return bool(getattr(target_user_obj, "is_bot", False))
    except Exception:
        pass

    row = get_user_row(int(target_id))
    return bool(row and int(row["is_bot"] or 0) == 1)

def _reply_is_direct_bot_without_targets(message, actor_id: int) -> bool:
    rm = getattr(message, "reply_to_message", None)
    if not rm:
        return False
    if is_channel_sender_message(rm):
        return False

    u = getattr(rm, "from_user", None)
    if not u or not bool(getattr(u, "is_bot", False)):
        return False

    if int(getattr(u, "id", 0) or 0) == int(actor_id):
        return False

    ids = _collect_reply_target_ids(message, exclude_user_ids={int(actor_id)})
    return len(ids) == 0

def _strict_single_target_token(token: str):
    tok = (token or "").strip()
    if not tok:
        return None

    tid = _resolve_or_create_infect_target(tok)
    if tid is not None:
        return int(tid)

    return None

def strict_single_target_args_ok(message, parsed: Optional["Parsed"], *, allow_empty: bool) -> bool:
    args = (parsed.args or "").strip() if parsed else ""

    if message.reply_to_message and message.reply_to_message.from_user:
        return not bool(args)

    if not args:
        return bool(allow_empty)

    return _resolve_single_target_from_text(args, _strict_single_target_token) is not None

def strict_single_numeric_arg_ok(parsed: Optional["Parsed"]) -> bool:
    args = (parsed.args or "").strip() if parsed else ""
    if not args:
        return False
    toks = args.split()
    return len(toks) == 1 and toks[0].isdigit()

def strict_single_word_arg_ok(parsed: Optional["Parsed"]) -> bool:
    args = (parsed.args or "").strip() if parsed else ""
    if not args:
        return False
    toks = args.split()
    return len(toks) == 1

def is_bot_target(target_id: Optional[int], target_user_obj, token: str = "") -> bool:
    try:
        my_bot_id = int(getattr(_me, "id", 0) or 0)
    except Exception:
        my_bot_id = 0

    if my_bot_id and target_id and int(target_id) == my_bot_id:
        return True

    if target_user_obj is not None and bool(getattr(target_user_obj, "is_bot", False)):
        return True

    tok = (token or "").strip()
    if tok.startswith("@") and tok[1:].lower().endswith("bot"):
        return True

    return False

def is_channel_sender_message(message) -> bool:
    try:
        sc = getattr(message, "sender_chat", None)
        if sc and (getattr(sc, "type", "") or "").lower() == "channel":
            return True
    except Exception:
        pass

    try:
        if bool(getattr(message, "is_automatic_forward", False)):
            return True
    except Exception:
        pass

    return False

def bot_cannot_have(what: str) -> str:
    return f"📑 Как бы вам и мне не хотелось, но бот не может участвовать в игре. У бота не может быть {what}"

def _pat_for_text(name: str) -> str:
    name = (name or "").strip()
    return f'патогеном «{h(name)}»' if name else "неизвестным патогеном"

def _pat_for_fever(name: str) -> str:
    name = (name or "").strip()
    return f"«{h(name)}»" if name else "неизвестным патогеном"

# PARSING COMMANDS / PREFIXES
@dataclass
class Parsed:
    raw: str
    has_prefix_char: bool          # '/' or '.'
    prefix_char: Optional[str]     # '/' or '.'
    cmd: str                       # normalized command key
    args: str                      # tail

def strip_bio_prefix(text: str) -> str:
    t = text.strip()
    m = re.match(r"^(био|бот)\s+(.*)$", t, flags=re.IGNORECASE)
    if m:
        return (m.group(2) or "").strip()
    return t

def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip())

def has_explicit_bot_prefix(text: str) -> bool:
    s = (text or "").strip()
    if not s:
        return False
    if s.startswith("/") or s.startswith("."):
        return True
    return bool(re.match(r"^(био|бот)\s+", s, flags=re.IGNORECASE))

def leading_sign_after_bot_prefix(text: str) -> str:
    s = normalize(text or "").strip()
    if not s:
        return ""

    s = strip_bio_prefix(s).lstrip()
    if not s:
        return ""

    if s.startswith("++"):
        return "+"
    if s[0] in "+-~":
        return s[0]
    return ""

SIGNED_COMMANDS_ALLOWED = {
    "timer_add_rel", "timer_add_abs", "timer_add_cycle", "timer_delete", "timer_clear_all",
    "chat_autodel_set", "chat_autodel_off",
    "balance_show", "balance_hide", "lab_show", "lab_hide",
    "notify_on", "notify_off",
    "corp_notify_on", "corp_notify_off",
    "rp_on", "rp_off",
    "mrp_add", "mrp_delete",
    "autoanswer_on", "autoanswer_off",
    "corp_open", "corp_close", "corp_rename",
    "corp_deputy", "corp_deputy_remove",
    "labname_clear", "pathogenname_clear",
    "chatname_set", "chatname_clear",
    "name_lock_user", "name_lock_lab", "name_lock_pat", "name_lock_corp",
    "upgrade_preview", "upgrade_buy",
}

def parse_message_as_command(text: str) -> Optional[Parsed]:
    if not text:
        return None
    
    raw_multiline = (text or "").strip()
    first_line_raw, _, _body_raw = raw_multiline.partition("\n")
    first_line = first_line_raw.strip()

    if normalize(first_line_raw).lower() == "!-игра вирусы":
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="lab_delete_now", args="")

    if first_line.startswith("/") or first_line.startswith("."):
        pch = first_line[0]
        body = first_line[1:].strip()

        nested = parse_message_as_command(body)
        if nested:
            return Parsed(
                raw=raw_multiline,
                has_prefix_char=True,
                prefix_char=pch,
                cmd=nested.cmd,
                args=nested.args
            )

        parts = body.split(" ", 1)
        c = parts[0].lower()
        a = parts[1].strip() if len(parts) > 1 else ""

        if c in (
            "owner", "owner_remove",
            "my_owner", "my_owner_remove",
            "agent", "агент", "agent_remove",
            "agents",
            "blacklist", "users", "bot_ban", "bot_unban", "remake_lab",
            "db_fife", "db_fife_stat", "db_fife_msg", "db_fife_upd", "its", "delete"
        ):
            cmd_map = {
                "owner": "owner",
                "owner_remove": "owner_remove",
                "my_owner": "my_owner",
                "my_owner_remove": "my_owner_remove",
                "agent": "agent",
                "агент": "agent",
                "agent_remove": "agent_remove",
                "agents": "agents_panel",
                "blacklist": "blacklist",
                "users": "users_list",
                "bot_ban": "bot_ban",
                "bot_unban": "bot_unban",
                "remake_lab": "remake_lab",
                "db_fife": "db_fife",
                "db_fife_stat": "db_fife_stat",
                "db_fife_msg": "db_fife_msg",
                "db_fife_upd": "db_fife_upd",
                "its": "its",
                "delete": "delete_user_db",
            }
            return Parsed(raw=raw_multiline, has_prefix_char=True, prefix_char=pch, cmd=cmd_map[c], args=a)

    raw = normalize(text)
    t = raw.strip()

    if t.startswith("/") or t.startswith("."):
        prefix_char = t[0]
        body = t[1:].strip()
        if not body:
            return None

        nested = parse_message_as_command(body)
        if nested:
            return Parsed(
                raw=raw,
                has_prefix_char=True,
                prefix_char=prefix_char,
                cmd=nested.cmd,
                args=nested.args
            )

        parts = body.split(" ", 1)
        c = parts[0].lower()
        a = parts[1].strip() if len(parts) > 1 else ""
        if c in ("owner", "owner_remove", "my_owner", "my_owner_remove", "agent", "агент", "agent_remove"):
            cmd_map = {
                "owner": "owner",
                "owner_remove": "owner_remove",
                "my_owner": "my_owner",
                "my_owner_remove": "my_owner_remove",
                "agent": "agent",
                "агент": "agent",
                "agent_remove": "agent_remove",
            }
            return Parsed(raw=raw, has_prefix_char=True, prefix_char=prefix_char, cmd=cmd_map[c], args=a)

        if c in ("bot_ban", "bot_unban", "remake_lab",
                 "db_fife", "db_fife_stat", "db_fife_msg", "db_fife_upd", "its"):
            return Parsed(raw=raw, has_prefix_char=True, prefix_char=prefix_char, cmd=c, args=a)

        if c == "delete":
            return Parsed(raw=raw, has_prefix_char=True, prefix_char=prefix_char, cmd="delete_user_db", args=a)
        return None

    t = strip_bio_prefix(t)

    # таймеры
    first_line = strip_bio_prefix(first_line)
    timer_head = first_line.strip()

    timer_sign = None
    if timer_head.startswith("++"):
        timer_sign = "++"
        timer_head = timer_head[2:].lstrip()
    elif timer_head.startswith(("+", "-", "!")):
        timer_sign = timer_head[0]
        timer_head = timer_head[1:].lstrip()

    timer_low = timer_head.lower()

    if timer_low == "таймеры":
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_list", args="")

    if timer_sign == "!" and timer_low in ("сбросить таймеры", "удалить все таймеры"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_clear_all", args="")

    if timer_sign == "-" and timer_low.startswith("таймер "):
        rest = timer_head.split(" ", 1)[1].strip() if " " in timer_head else ""
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_delete", args=rest)

    if (timer_sign in (None, "+")) and timer_low.startswith("таймер цикл "):
        rest = timer_head[len("таймер цикл "):].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_add_cycle", args=rest)

    if (timer_sign in (None, "+")) and timer_low.startswith("таймер через "):
        rest = timer_head[len("таймер через "):].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_add_rel", args=rest)

    if (timer_sign in (None, "+")) and timer_low.startswith("таймер на "):
        rest = timer_head[len("таймер на "):].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="timer_add_abs", args=rest)

    sign = None
    if t.startswith("++"):
        sign = "++"
        t = t[2:].lstrip()
    elif t.startswith(("+", "-", "!", "~")):
        sign = t[0]
        t = t[1:].lstrip()

    low = t.lower()

    # автоудаление
    if sign == "+" and (low == "автоудаление" or low == "ау" or low.startswith("автоудаление ") or low.startswith("ау ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chat_autodel_set", args=rest)

    if sign == "-" and low in ("автоудаление", "ау"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chat_autodel_off", args="")

    if low in ("автоудаление", "ау"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chat_autodel_status", args="")

    # команды лс
    if low in ("settings", "настройки"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="settings", args="")

    if low in ("report", "репорт"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="report", args="")

    if low in ("agents", "агенты"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="agents_panel", args="")

    if low == "my_owner":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="my_owner", args="")

    if low == "my_owner_remove":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="my_owner_remove", args="")

    if low == "owner" or low.startswith("owner "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="owner", args=rest)

    if low.startswith("owner_remove"):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="owner_remove", args=rest)

    if low == "agent" or low == "агент" or low.startswith("agent ") or low.startswith("агент "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="agent", args=rest)

    if low.startswith("agent_remove"):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="agent_remove", args=rest)

    if low == "blacklist":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="blacklist", args="")

    if sign in ("+", "-") and (low == "lab_name" or low.startswith("lab_name ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(
            raw=raw_multiline,
            has_prefix_char=False,
            prefix_char=None,
            cmd="name_lock_lab",
            args=rest
        )

    if sign in ("+", "-") and (low == "pat_name" or low.startswith("pat_name ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(
            raw=raw_multiline,
            has_prefix_char=False,
            prefix_char=None,
            cmd="name_lock_pat",
            args=rest
        )

    if sign in ("+", "-") and (low == "user_name" or low.startswith("user_name ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(
            raw=raw_multiline,
            has_prefix_char=False,
            prefix_char=None,
            cmd="name_lock_user",
            args=rest
        )

    if sign in ("+", "-") and (low == "corp_name" or low.startswith("corp_name ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(
            raw=raw_multiline,
            has_prefix_char=False,
            prefix_char=None,
            cmd="name_lock_corp",
            args=rest
        )

    #команды помощи
    if low in ("помощь", "help"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="help", args="")

    if low == "пинг":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="ping", args="")

    if low in ("команды", "commands"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="commands_link", args="")

    if low in ("рпстат", "рпстата", "рп стата", "рп стат"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="rp_stats", args="")

    if (
        low in ("патогены", "паты", "заряды", "патроны")
        or low.startswith("патогены ")
        or low.startswith("паты ")
        or low.startswith("заряды ")
        or low.startswith("патроны ")
    ):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="pathogens_info", args=rest)

    if low in ("патоген инфо", "пат инфо", "пи"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="pathogen_info", args="")

    if low.startswith("пак айди ") or low.startswith("пак ид ") or low.startswith("пак id ") \
       or low.startswith("эмодзипак айди ") or low.startswith("эмодзипак ид ") or low.startswith("эмодзипак id "):
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            if parts[0].lower() in ("пак", "эмодзипак"):
                return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="emoji_pack_ids", args=parts[2].strip())

    # дуэли
    if low in ("выстрел", "дуэль выстрел"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_fire", args="")

    if low in ("прицелиться", "прицел", "дуэль прицелиться", "дуэль прицел"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_aim", args="")

    if low in ("сбить прицел", "дуэль сбить прицел"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_break_aim", args="")

    if low in ("сдаться", "дуэль сдаться"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_surrender", args="")

    if low in ("дуэли стата", "дуэль стата", "дуэли стат", "дуэль стат"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_stats", args="")

    if low in ("дуэль да", "дуэль принять"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_accept", args="")

    if low in ("дуэль отмена", "дуэль отменить"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_cancel", args="")

    if low in ("дуэли ставки", "ставки дуэлей", "дуэль ставки"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_bets_list", args="")

    if low in ("дуэль нет", "дуэль отказ", "дуэль отказаться", "дуэль отказать"):
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_decline", args="")

    if low == "дуэль":
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_call", args="")
    
    if low.startswith("дуэль ставка "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_bet", args=rest)
    
    if low.startswith("ставка "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="duel_bet", args=rest)
    
    if low.startswith("дуэль "):
        rest = t.split(" ", 1)[1].strip()
        first_tok = rest.split(None, 1)[0] if rest else ""
        cmd = "duel_call_stake" if first_tok.isdigit() else "duel_call"
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd=cmd, args=rest)

    # агент команды
    if low == "bot_ban" or low.startswith("bot_ban "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="bot_ban", args=rest)

    if low == "bot_unban" or low.startswith("bot_unban "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="bot_unban", args=rest)

    if low == "remake_lab" or low.startswith("remake_lab "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="remake_lab", args=rest)

    if low == "cof_inf_stats":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="cof_inf_stats", args="")

    if low == "duel_cof_stats":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_cof_stats", args="")

    if low.startswith("edit_k "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="edit_k", args=t.split(" ", 1)[1].strip())

    if low.startswith("edit_b "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="edit_b", args=t.split(" ", 1)[1].strip())

    if low.startswith("duel_cof_break "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_cof_break", args=t.split(" ", 1)[1].strip())

    if low.startswith("duel_cof_break_bon "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_cof_break_bon", args=t.split(" ", 1)[1].strip())

    if low.startswith("duel_cof_aim "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_cof_aim", args=t.split(" ", 1)[1].strip())

    if low.startswith("duel_cof_base_pts "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_cof_base_pts", args=t.split(" ", 1)[1].strip())

    if low.startswith("duel_rounds "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="duel_rounds", args=t.split(" ", 1)[1].strip())

    # удаление лабы
    if t == LAB_DELETE_PHRASE:
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_delete_confirm_phrase", args="")

    # промокоды
    if low == "promocode_generate":
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="promo_generate", args="")

    if low == "promocode_all":
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="promo_all", args="")

    if low == "promocode_delete" or low.startswith("promocode_delete "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="promo_delete", args=rest)

    if low == "promocode_create" or low.startswith("promocode_create "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="promo_create", args=rest)

    if low == "promo" or low.startswith("promo "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="promo_use", args=rest)

    # приватные настройки
    if sign in ("+", "-"):
        if low in ("баланс", "мешок", "кошелек", "кошелёк", "кош", "бал", "меш"):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                          cmd=("balance_show" if sign == "+" else "balance_hide"), args="")
        if low in ("лаб", "лаборатория", "лаба"):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                          cmd=("lab_show" if sign == "+" else "lab_hide"), args="")

    if low.startswith("скрыть"):
        if ("баланс" in low) or ("мешок" in low) or ("кошелек" in low) or ("кошелёк" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="balance_hide", args="")
        if ("лаб" in low) or ("лабораторию" in low) or ("лабу" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_hide", args="")

    if low.startswith("показать"):
        if ("баланс" in low) or ("мешок" in low) or ("кошелек" in low) or ("кошелёк" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="balance_show", args="")
        if ("лаб" in low) or ("лабораторию" in low) or ("лабу" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_show", args="")



    # улучшения навыков
    if sign in ("+", "++"):
        first = low.split(" ", 1)[0]
        if _resolve_skill(first):
            return Parsed(
                raw=raw,
                has_prefix_char=False,
                prefix_char=None,
                cmd=("upgrade_buy" if sign == "++" else "upgrade_preview"),
                args=low
            )
        
    # уведомления
    if sign in ("+", "-") and low in ("уведомления", "уведы"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("notify_on" if sign == "+" else "notify_off"), args="")

    if sign in ("+", "-") and low in ("корп уведы", "корп уведомления", "корп уведомление"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("corp_notify_on" if sign == "+" else "corp_notify_off"), args="")

    # рп
    if sign in ("+", "-") and low == "рп":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("rp_on" if sign == "+" else "rp_off"), args="")

    # мрп
    if sign == "+" and (low == "мрп" or low.startswith("мрп ")):
        rest = ""
        if " " in t:
            rest = t.split(" ", 1)[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="mrp_add", args=rest)

    if sign == "-" and (low == "мрп" or low.startswith("мрп ")):
        rest = ""
        if " " in t:
            rest = t.split(" ", 1)[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="mrp_delete", args=rest)

    if low == "мрп":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="mrp_list", args="")

    # автоответчик
    if sign in ("+", "-") and low in ("автоответчик", "ао", "заражалка", "автозаражалка", "авто заражалка", "аз"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("autoanswer_on" if sign == "+" else "autoanswer_off"), args="")
    if low in ("автоответчик", "ао", "заражалка", "автозаражалка", "авто заражалка", "аз"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="autoanswer_status", args="")

    # калькулятор
    if low in ("к", "калькулятор", "ку", "кпк", "кш", "кпц", "ко", "кдл"):
        calc_cmd = "calc"
        if low in ("ку", "кпк"):
            calc_cmd = "calc_upg"
        elif low in ("кш", "кпц"):
            calc_cmd = "calc_chance"
        elif low == "ко":
            calc_cmd = "calc_exp"
        elif low == "кдл":
            calc_cmd = "calc_duel"
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd=calc_cmd, args="")
    if low in ("кс", "кус"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_buff", args="")

    if low.startswith("калькулятор усилений "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_buff", args=t.split(" ", 2)[2].strip())
    if low.startswith("калькулятор усиления "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_buff", args=t.split(" ", 2)[2].strip())
    if low.startswith("кс "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_buff", args=t.split(" ", 1)[1].strip())
    if low.startswith("кус "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_buff", args=t.split(" ", 1)[1].strip())

    if low.startswith("калькулятор "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc", args=t.split(" ", 1)[1].strip())
    if low.startswith("к "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc", args=t.split(" ", 1)[1].strip())
    if low.startswith("ку "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_upg", args=t.split(" ", 1)[1].strip())
    if low.startswith("кпк "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_upg", args=t.split(" ", 1)[1].strip())
    if low.startswith("кш "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_chance", args=t.split(" ", 1)[1].strip())
    if low.startswith("кпц "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_chance", args=t.split(" ", 1)[1].strip())
    if low.startswith("ко "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_exp", args=t.split(" ", 1)[1].strip())
    if low.startswith("кдл "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc_duel", args=t.split(" ", 1)[1].strip())

    # заразить
    if low == "заразить" or low.startswith("заразить "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="infect", args=rest)    

    # диверсия
    if low in ("див", "диверсия") or low.startswith(("див ", "диверсия ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="sabotage", args=rest)

    # корпорации
    if low.startswith(("создать корпорацию", "создать корпорацию ", 
                       "создать корп", "создать корп ", 
                       "создать корпу", "создать корпу ", 
                       "создать к", "создать к ")):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_create", args=rest)

    if sign == "~" and (
        low == "корп название"
        or low == "корпорация название"
        or low == "к название"
        or low.startswith("корп название ")
        or low.startswith("корпорация название ")
        or low.startswith("к название ")
    ):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="corp_rename", args=rest)

    if low in ("удалить корпорацию", "удалить корп", "удалить корпу", "удалить к"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_delete", args="")

    if sign in ("+", "-") and low in ("корп", "корпорация", "корпа", "к"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("corp_open" if sign == "+" else "corp_close"), args="")
    if low.startswith(("открыть корп", "открыть корпорацию", 
                       "открыть корпу", "открыть к")):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_open", args="")
    if low.startswith(("закрыть корп", "закрыть корпорацию", 
                       "закрыть корпу", "закрыть к")):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_close", args="")

    if low.startswith(("корп рег", "корпорация рег", "ркорп", "к рег")):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_reg", args=rest)

    if low in ("моя корп", "моя корпорация", "моя корпа", "моя к"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_my", args="")

    if low in ("моя корп", "моя корпорация", "моя корпа", "моя к"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_my", args="")

    if low in ("исключить", "корп кик") or low.startswith(("исключить ", "корп кик ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_kick", args=rest)

    if low in ("корп заявки", "корпорация заявки"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_req_list", args="")

    if low in ("корп покинуть", "корпорация покинуть", "корп выйти", "корпорация выйти", "покинуть", "выйти"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_leave", args="")

    if low in ("корп инфо", "корпорация инфо", "икорп", "к инфо", "досье корп", "досье корпорации"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_info", args="")

    if low.startswith(("корп инфо ", "корпорация инфо ", "икорп ", "к инфо ", "досье корп ", "досье корпорации ")):
        prefixes = (
            "корп инфо ", "корпорация инфо ", "икорп ", "к инфо ",
            "досье корп ", "досье корпорации "
        )
        rest = ""
        for pref in prefixes:
            if low.startswith(pref):
                rest = t[len(pref):].strip()
                break
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_info", args=rest)

    if low in ("корп", "корпорация", "корпа", "к"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_info", args="")

    if low.startswith(("корп ", "корпорация ", "корпа ", "к ")):
        rest = t.split(" ", 1)[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_info", args=rest)

    if low == "вступить" or low.startswith("вступить "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_join", args=rest)

    if low == "принять" or low.startswith("принять "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_req_accept", args=rest)

    if low == "отказать" or low.startswith("отказать "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_req_reject", args=rest)

    if low == "пригласить" or low.startswith("пригласить "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_invite", args=rest)

    if sign == "+" and low in ("корп зам", "корп заместитель", "зам", "заместитель"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy", args="")

    if sign == "+" and (low.startswith(("корп зам ", "зам ")) or low.startswith(("корп заместитель ", "заместитель "))):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy", args=rest)

    if sign == "-" and low in ("корп зам", "корп заместитель", "зам", "заместитель"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy_remove", args="")

    if sign == "-" and (low.startswith(("корп зам ", "зам ")) or low.startswith(("корп заместитель ", "заместитель "))):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy_remove", args=rest)

    if low == "передать права" or low.startswith("передать права "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_transfer_owner", args=rest)

    if low == "передать владельца" or low.startswith("передать владельца "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_transfer_owner", args=rest)

    if low.startswith("передать р "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_send_res", args=rest)

    if low.startswith("передать м "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_send_mat", args=rest)

    # топы
    if low in ("стата", "топ") or low.startswith(("стата ", "топ ")):
        toks = low.split()

        if len(toks) >= 3 and toks[1] in ("корп", "корпораций", "к") and toks[2] == "чата":
            rest = toks[3] if len(toks) >= 4 and toks[3].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_corps_chat", args=rest)

        if len(toks) >= 2 and toks[1] in ("корп", "корпораций", "к"):
            rest = toks[2] if len(toks) >= 3 and toks[2].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_corps", args=rest)

        if len(toks) >= 3 and toks[1] in ("болезней", "болезни", "б", "патогенов", "патогены", "паты", "патов") and toks[2] == "чата":
            rest = toks[3] if len(toks) >= 4 and toks[3].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_diseases_chat", args=rest)

        if len(toks) >= 2 and toks[1] in ("болезней", "болезни", "б", "патогенов", "патогены", "паты", "патов"):
            rest = toks[2] if len(toks) >= 3 and toks[2].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_diseases", args=rest)

        if len(toks) >= 2 and toks[1] == "чата":
            rest = toks[2] if len(toks) >= 3 and toks[2].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_users_chat", args=rest)

        rest = toks[1] if len(toks) >= 2 and toks[1].isdigit() else ""
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_users", args=rest)

    # баланс
    if low in ("мешок", "баланс", 
               "кошелек", "кошелёк", 
               "кеш", "бал", "меш") or low.startswith(
                   ("мешок ", "баланс ", 
                    "кошелек ", "кошелёк ",
                    "кеш ", "бал ", "меш ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="balance", args=rest)

    # синтез
    if low == "синтез" or low.startswith("синтез "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="synth", args=rest)

    # купить вакцину
    if low == "купить вакцину" or low.startswith("купить вакцину"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="buy_vaccine", args="")

    # использовать вакцину
    if low in ("использовать вакцину", "использовать вакцин") or low.startswith(
        ("использовать вакцину ", "использовать вакцин ")
    ):
        rest = ""
        parts = t.split(" ", 2)
    
        if low.startswith(("использовать вакцину ", "использовать вакцин ")):
            if len(parts) >= 3:
                rest = parts[2].strip()
        else:
            if len(parts) >= 2:
                rest = parts[1].strip()
    
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="use_vaccine", args=rest)

    # модерирование
    if low in ("удалить лабу", "удалить лабораторию", "удалить лаб"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_delete", args="")

    if low in ("восстановить лабу", "восстановить лабораторию", "восстановить лаб"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="restore_lab", args="")

    # "моя лаба" / "моя лаборатория"
    if low.startswith("моя лаба") or low.startswith("моя лаборатория") or low.startswith("моя л") or low.startswith("моя лаб"):
        args = t.split(" ", 2)
        rest = ""
        if len(args) > 2:
            rest = args[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="mylab", args=rest)

    # "лаб" / "лаборатория"
    if low == "лаб" or low.startswith("лаб ") or low == "лаборатория" or low.startswith("лаборатория "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab", args=rest)

    # "-имя лабы" / "-имя лаборатории" / "-имя пата" / "-имя патогена"
    if sign == "-" and (
        low == "имя лабы"
        or low == "имя лаборатории"
        or low.startswith("имя лабы ")
        or low.startswith("имя лаборатории ")
    ):
        rest = ""
        spl = t.split(" ", 2)
        if len(spl) == 3:
            rest = spl[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="labname_clear", args=rest)

    if sign == "-" and (
        low == "имя пата"
        or low == "имя патогена"
        or low == "имя болезни"
        or low.startswith("имя пата ")
        or low.startswith("имя патогена ")
        or low.startswith("имя болезни ")
    ):
        rest = ""
        spl = t.split(" ", 2)
        if len(spl) == 3:
            rest = spl[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="pathogenname_clear", args=rest)

    # "имя лабы" / "имя лаборатории"
    if low.startswith("имя лабы") or low.startswith("имя лаборатории"):
        rest = ""
        spl = t.split(" ", 2)
        if len(spl) == 3:
            rest = spl[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="labname", args=rest)

    # "имя пата" / "имя патогена"
    if low.startswith("имя пата") or low.startswith("имя патогена") or low.startswith("имя болезни"):
        rest = ""
        spl = t.split(" ", 2)
        if len(spl) == 3:
            rest = spl[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="pathogenname", args=rest)

    # "+имя" / "-имя" / "имя" / "текущее имя"
    if sign == "+" and (low == "имя" or low.startswith("имя ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chatname_set", args=rest)

    if sign == "-" and (low == "имя" or low.startswith("имя ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chatname_clear", args=rest)

    if low == "имя" or low.startswith("имя "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chatname_show", args=rest)

    if low == "текущее имя" or low.startswith("текущее имя "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) == 3:
            rest = parts[2].strip()
        return Parsed(raw=raw_multiline, has_prefix_char=False, prefix_char=None, cmd="chatname_show", args=rest)

    # пол
    if low == "мой пол" or low.startswith("мой пол "):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="gender_set", args=rest)

    return None

# MRP FILTER
def is_reserved_bot_or_rp_trigger(text: str) -> bool:
    s = strip_bio_prefix((text or "").strip())
    if not s:
        return False

    first, _, _ = s.partition("\n")
    probe = first.strip()
    if not probe:
        return False

    parsed = parse_message_as_command(probe)
    if parsed is not None:
        return True

    action = get_rp_action(probe)
    if action is not None:
        return True

    return False

def is_reserved_for_personal_rp(user_id: int, trigger: str) -> bool:
    probe = _normalize_rp_trigger(trigger)
    if not probe:
        return True

    if is_reserved_bot_or_rp_trigger(probe):
        return True

    row = db_one(
        "SELECT 1 FROM personal_rp_actions WHERE user_id=? AND trigger_key=? LIMIT 1",
        (int(user_id), probe)
    )
    return row is not None

# START MESSAGE / SUPPORT LIST
def split_agents_by_online(agents: List[sqlite3.Row]) -> Tuple[List[sqlite3.Row], List[sqlite3.Row]]:
    online, offline = [], []
    cutoff = now_ts() - ONLINE_TTL_SECONDS
    for a in agents:
        last_seen = int(a["last_seen"] or 0)
        if last_seen >= cutoff:
            online.append(a)
        else:
            offline.append(a)
    return online, offline

def format_agent_line(a: sqlite3.Row) -> str:
    uid = int(a["user_id"])
    fn = (a["first_name"] or "").strip()
    ln = (a["last_name"] or "").strip()
    username = (a["username"] or "").strip()
    name = standard_display_name(fn, ln, username, uid)
    return tg_mention(uid, name, username=username)

def _panel_role_row(user_id: int, role_text: str):
    uid = int(user_id)
    row = get_user_row(uid)
    return {
        "user_id": uid,
        "username": (row["username"] or "") if row else "",
        "first_name": (row["first_name"] or "") if row else "",
        "last_name": (row["last_name"] or "") if row else "",
        "last_seen": int(row["last_seen"] or 0) if row else 0,
        "role_text": str(role_text or "").strip(),
    }

def _panel_owner_rows(exclude_user_id: int = 0):
    rows = []
    creator_id = int(get_current_creator_id())

    rows.append(_panel_role_row(creator_id, "создатель"))

    for r in get_bot_owners():
        uid = int(r["user_id"])
        if uid == creator_id:
            continue
        rows.append(_panel_role_row(uid, "старший агент"))

    out = []
    seen = set()
    for r in rows:
        uid = int(r["user_id"])
        if uid == int(exclude_user_id):
            continue
        if uid in seen:
            continue
        seen.add(uid)
        out.append(r)
    return out

def build_start_text(user) -> str:
    support_rows = []
    seen = set()

    for r in _panel_owner_rows(0):
        uid = int(r["user_id"])
        if uid in seen:
            continue
        seen.add(uid)
        support_rows.append(r)

    for r in get_support_agents():
        uid = int(r["user_id"])
        if uid in seen:
            continue
        seen.add(uid)
        support_rows.append(r)

    online, offline = split_agents_by_online(support_rows)

    u_name = user_full_name(user)

    def _support_line(a) -> str:
        prefix = ""
        return prefix + format_agent_line(a)

    lines = []
    lines.append(f'👋 Приветствуем вас, <b>{h(u_name)}</b>, в {h(BOT_TITLE)}')
    lines.append(f'Я создан на основе старой игры бота <a href="{h(IRIS_BOT_LINK)}">Iris | Чат-менеджер</a> с некоторыми доработками.\n')
    lines.append("Что вас интересует?")
    lines.append(f'1. <code>Био настройки</code> — более гибкая настройка параметров уведомлений и прочего.')
    lines.append(f'2. <code>Био репорт</code> — если заметили, что в моей работе что-то не так, уведомите тех.поддержку.\n')

    lines.append('👨‍⚕️ <b>Агенты поддержки</b>, которые могут ответить на ваши вопросы')

    if not online and not offline:
        lines.append("Список пока пуст.")
    else:
        if online:
            lines.append("🟢 Онлайн")
            lines.extend([_support_line(a) for a in online])
        if offline:
            lines.append("🔘 Оффлайн")
            lines.extend([_support_line(a) for a in offline])

    lines.append("")
    lines.append(f'📑 Список всех команд <a href="{h(URL_COMMANDS)}">с их описанием</a>')
    lines.append(f'📑 Чат <a href="{h(URL_SUPPORT_CHAT)}">тех.поддержки</a>')
    lines.append(f'📑 Основной <a href="{h(URL_DEV_CHANNEL)}">канал разработки бота</a>')
    lines.append(f'💬 Для повторного вызова агент-листа, введите в чат \"<code>.помощь</code>\"')

    return "\n".join(lines)

def add_to_chat_keyboard() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    if BOT_USERNAME:
        url = f"https://t.me/{BOT_USERNAME}?startgroup=1"
    else:
        url = "https://t.me/"
    kb.add(InlineKeyboardButton("Добавить в свой чат", url=url, style="success"))
    return kb

def send_welcome_message(chat_id: int, user):
    text = build_start_text(user)
    bot.send_message(
        chat_id,
        text,
        reply_markup=add_to_chat_keyboard(),
        disable_web_page_preview=True,
    )

def handle_help_command(message):
    upsert_user(message.from_user)
    ensure_creator_is_support()
    if message.chat.type == "private":
        ensure_lab_exists(int(message.from_user.id))
    send_welcome_message(int(message.chat.id), message.from_user)

def _format_ping_seconds_ms(delta_ms: int) -> str:
    delta_ms = max(0, int(delta_ms or 0))
    sec = delta_ms // 1000
    ms = delta_ms % 1000

    if ms == 0:
        return f"{sec} {_ru_form(sec, 'секунда', 'секунды', 'секунд')}"

    return f"{sec},{ms:03d} секунды"

def handle_ping_command(message):
    started = time.perf_counter()

    text = "ПОНГ\nВремя ответа: 0,000 секунды"
    sent = bot.reply_to(message, text)

    delta_ms = int(round((time.perf_counter() - started) * 1000))
    final_text = f"ПОНГ\nВремя ответа: {_format_ping_seconds_ms(delta_ms)}"

    try:
        limited_edit_message_text(
            text=final_text,
            chat_id=int(sent.chat.id),
            msg_id=int(sent.message_id),
            parse_mode="HTML",
            reply_markup=None,
            disable_web_page_preview=True
        )
    except Exception:
        try:
            bot.edit_message_text(
                final_text,
                chat_id=int(sent.chat.id),
                message_id=int(sent.message_id)
            )
        except Exception:
            pass

def handle_commands_link(message):
    bot.reply_to(
        message,
        f'📑 Список <a href="{h(URL_COMMANDS)}">команд бота</a>',
        parse_mode="HTML",
        disable_web_page_preview=False
    )

# EMOJI 
def _extract_emoji_pack_name_and_url(text: str) -> tuple[str, str]:
    s = (text or "").strip()
    if not s:
        return "", ""

    toks = s.split()
    if len(toks) != 1:
        return "", ""

    token = toks[0].strip()

    m = re.match(r"^(?:https?://)?t\.me/addemoji/([A-Za-z0-9_]{1,64})/?$", token, flags=re.IGNORECASE)
    if m:
        short_name = m.group(1)
        return short_name, token if token.startswith(("http://", "https://")) else f"https://t.me/addemoji/{short_name}"

    m = re.match(r"^(?:https?://)?t\.me/addstickers/([A-Za-z0-9_]{1,64})/?$", token, flags=re.IGNORECASE)
    if m:
        short_name = m.group(1)
        return short_name, token if token.startswith(("http://", "https://")) else f"https://t.me/addstickers/{short_name}"

    # fallback: allow plain short name
    if re.fullmatch(r"[A-Za-z0-9_]{1,64}", token):
        return token, f"https://t.me/addemoji/{token}"

    return "", ""

def _custom_pack_emoji_html(emoji_fallback: str, custom_emoji_id: str) -> str:
    emo = (emoji_fallback or "🙂").strip() or "🙂"
    ceid = (custom_emoji_id or "").strip()
    if PREMIUM_EMOJI_ENABLED and ceid:
        return f'<tg-emoji emoji-id="{h(ceid)}">{h(emo)}</tg-emoji>'
    return h(emo)

def _emoji_pack_cache_key(short_name: str) -> str:
    s = re.sub(r"[^A-Za-z0-9_]", "", (short_name or "").strip())
    return s[:40] if s else "pack"

def _emoji_pack_cb(cache_key: str, page: int) -> str:
    return f"{EMPACKUI_TAG}:{cache_key}:{int(page)}"

def _emoji_pack_parse_cb(data: str) -> tuple[str, Optional[int]]:
    try:
        p = (data or "").split(":")
        if len(p) != 3 or p[0] != EMPACKUI_TAG:
            return "", None
        return p[1], int(p[2])
    except Exception:
        return "", None

def _collect_custom_emoji_items(stickers: list) -> list[tuple[str, str]]:
    items = []
    for st in (stickers or []):
        ceid = str(getattr(st, "custom_emoji_id", "") or "").strip()
        if not ceid:
            continue
        fallback_emoji = str(getattr(st, "emoji", "") or "🙂")
        items.append((fallback_emoji, ceid))
    return items

def kb_emoji_pack_pages(cache_key: str, page: int, total_pages: int) -> Optional[InlineKeyboardMarkup]:
    if total_pages <= 1:
        return None

    page = max(1, min(int(page), int(total_pages)))
    kb = InlineKeyboardMarkup(row_width=8)
    row_btns = []

    if page > 2:
        row_btns.append(InlineKeyboardButton("<<", callback_data=_emoji_pack_cb(cache_key, 1)))
    if page > 1:
        row_btns.append(InlineKeyboardButton("<", callback_data=_emoji_pack_cb(cache_key, page - 1)))

    page_nums = [page]
    if page == 1:
        page_nums.extend([p for p in (2, 3, 4) if p <= total_pages])
    elif page == total_pages:
        page_nums = [p for p in (max(1, page - 3), max(1, page - 2), max(1, page - 1), page) if p <= total_pages]
    else:
        candidates = [page - 1, page, page + 1, page + 2]
        page_nums = [p for p in candidates if 1 <= p <= total_pages]

    page_nums = sorted(dict.fromkeys(page_nums))
    for p in page_nums:
        if p == page:
            row_btns.append(InlineKeyboardButton(f"·{p}·", callback_data=_emoji_pack_cb(cache_key, page)))
        else:
            row_btns.append(InlineKeyboardButton(str(p), callback_data=_emoji_pack_cb(cache_key, p)))

    if page < total_pages:
        row_btns.append(InlineKeyboardButton(">", callback_data=_emoji_pack_cb(cache_key, page + 1)))
    if page < total_pages - 1:
        row_btns.append(InlineKeyboardButton(">>", callback_data=_emoji_pack_cb(cache_key, total_pages)))

    kb.row(*row_btns)
    return kb

def render_emoji_pack_ids_page(pack_title: str, pack_url: str, items: list, page: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    title_link = f'<a href="{h(pack_url)}">{h(pack_title)}</a>' if pack_url else h(pack_title)

    total = len(items)
    total_pages = max(1, (total + EMOJI_PACK_PAGE_SIZE - 1) // EMOJI_PACK_PAGE_SIZE)
    page = max(1, min(int(page), total_pages))
    start = (page - 1) * EMOJI_PACK_PAGE_SIZE
    part = items[start:start + EMOJI_PACK_PAGE_SIZE]

    lines = [f"📋 Список всех премиум эмодзи пака {title_link}", ""]

    if not items:
        lines.append("<blockquote expandable>Список пуст.</blockquote>")
        return "\n".join(lines), None

    lines.append("<blockquote expandable>")
    for idx, (fallback_emoji, ceid) in enumerate(part, start + 1):
        emo = _custom_pack_emoji_html(fallback_emoji, ceid)
        lines.append(f"{idx}|{emo}|<code>{h(ceid)}</code>")

    lines.append("</blockquote>")

    kb = None
    if total_pages > 1:
        cache_key = ""
        for k, v in _EMOJI_PACK_VIEW_CACHE.items():
            if v.get("title") == pack_title and v.get("url") == pack_url and v.get("items") == items:
                cache_key = k
                break
        if cache_key:
            kb = kb_emoji_pack_pages(cache_key, page, total_pages)

    return "\n".join(lines), kb

def handle_rp_stats_command(message):
    chat_type = (getattr(message.chat, "type", "") or "").lower()
    if chat_type not in ("private", "group", "supergroup"):
        return
    if is_channel_sender_message(message):
        return
    if getattr(message, "from_user", None) is None:
        return

    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    try:
        sent = _REAL_BOT_REPLY_TO(
            message,
            premiumize_html_text(render_rp_stats_text(uid)),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        remember_reply_pair_for_autodelete(sent, message)
    except Exception:
        return

def handle_emoji_pack_ids_command(message, parsed: Parsed):
    short_name, pack_url = _extract_emoji_pack_name_and_url((parsed.args or "").strip())
    if not short_name:
        bot.reply_to(
            message,
            "📑 Укажите одну ссылку на эмодзи-пак Telegram после команды.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    try:
        st_set = bot.get_sticker_set(short_name)
    except Exception:
        bot.reply_to(
            message,
            "📑 Не удалось открыть указанный эмодзи-пак.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    title = str(getattr(st_set, "title", "") or short_name)
    stickers = list(getattr(st_set, "stickers", None) or [])
    items = _collect_custom_emoji_items(stickers)

    cache_key = _emoji_pack_cache_key(short_name)
    _EMOJI_PACK_VIEW_CACHE[cache_key] = {
        "short_name": short_name,
        "title": title,
        "url": pack_url,
        "items": items,
        "updated_at": int(now_ts())
    }

    text, rm = render_emoji_pack_ids_page(title, pack_url, items, 1)

    bot.reply_to(
        message,
        text,
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=rm
    )

def handle_mrp_add_command(message):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    parsed_payload = _parse_mrp_create_from_text(message.text or "")
    if not parsed_payload:
        bot.reply_to(
            message,
            "📑 Неверный формат.\nИспользуйте <code>+Мрп</code> [название] / [эмодзи] [айди премиум эмодзи (не обязятельно)] / [текст рп действия].",
            parse_mode="HTML"
        )
        return

    trigger = parsed_payload["trigger"]
    trigger_key = parsed_payload["trigger_key"]
    emoji = parsed_payload["emoji"]
    premium_id = parsed_payload["premium_id"]
    action_text = parsed_payload["action_text"]

    cnt_row = db_one("SELECT COUNT(*) AS c FROM personal_rp_actions WHERE user_id=?", (uid,))
    cnt = int(cnt_row["c"] or 0) if cnt_row else 0
    if cnt >= 50:
        bot.reply_to(message, "📑 Достигнут лимит личных рп команд.\n💬 Чтобы освободить место под новые команды, введи\n <code>-Мрп</code> <b>[название / номер]</b>", parse_mode="HTML")
        return

    if is_reserved_for_personal_rp(uid, trigger):
        bot.reply_to(message, "📑 Этот триггер уже занят командой бота, глобальной рп-командой или вашей личной рп-командой.")
        return

    db_exec(
        "INSERT INTO personal_rp_actions(user_id, trigger, trigger_key, emoji, premium_id, action_text, uses_count, created_at) "
        "VALUES (?,?,?,?,?,?,0,?)",
        (uid, trigger, trigger_key, emoji, premium_id, action_text, int(now_ts())),
        commit=True
    )

    bot.reply_to(message, f"✅ Личная рп команда <code>{h(trigger)}</code> успешно создана.", parse_mode="HTML")

def handle_mrp_delete_command(message, parsed: Parsed):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    arg = (parsed.args or "").strip()
    if not arg:
        return

    rows = db_all(
        "SELECT action_id, trigger, trigger_key FROM personal_rp_actions WHERE user_id=? ORDER BY action_id ASC",
        (uid,)
    ) or []

    target_id = None

    if arg.isdigit():
        idx = int(arg)
        if 1 <= idx <= len(rows):
            target_id = int(rows[idx - 1]["action_id"])
    else:
        probe = _normalize_rp_trigger(arg)
        for r in rows:
            if _normalize_rp_trigger(r["trigger"] or "") == probe:
                target_id = int(r["action_id"])
                break

    if target_id is None:
        bot.reply_to(message, "📑 Личная рп команда не найдена.")
        return

    db_exec("DELETE FROM personal_rp_actions WHERE action_id=? AND user_id=?", (int(target_id), uid), commit=True)
    bot.reply_to(message, "✅ Личная рп команда удалена.")

def handle_mrp_list_command(message):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    text = render_personal_rp_list_text(uid)
    pm_kb = kb_open_bot_pm()

    if message.chat.type == "private":
        bot.reply_to(
            message,
            text,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    try:
        _REAL_BOT_SEND_MESSAGE(
            uid,
            text,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        bot.reply_to(
            message,
            "📋 Список личных рп команд отправлен в личные сообщения.",
            reply_markup=pm_kb
        )
    except Exception:
        bot.reply_to(
            message,
            "📑 Не удалось отправить список в личные сообщения. Напишите боту в л/с.",
            reply_markup=pm_kb
        )

def try_handle_rp_action_message(message) -> bool:
    chat_type = (getattr(message.chat, "type", "") or "").lower()
    if chat_type not in ("private", "group", "supergroup"):
        return False
    if is_channel_sender_message(message):
        return False

    actor = getattr(message, "from_user", None)
    if actor is None:
        return False

    actor_id = int(actor.id)
    upsert_user(actor)
    
    action, tail, comment_text = _parse_rp_message(message.text or "", actor_id)
    if not action:
        return False
    
    if rp_commands_enabled(int(actor_id)) != 1:
        return True
    
    target_id, target_user_obj = resolve_rp_target(message, actor_id, tail)
    if target_id is None:
        return False
    
    if int(target_id) == int(actor_id):
        return False
    
    if rp_commands_enabled(int(target_id)) != 1:
        bot.reply_to(message, "📑 Этот пользователь отключил РП-команды.")
        return True

    if target_user_obj is not None:
        capture_user_context(message, target_user_obj)

    actor_tag = _rp_actor_tag(actor)
    target_tag = public_user_tag(int(target_id))

    if getattr(message, "reply_to_message", None):
        extra_tail = (tail or "").strip()
    else:
        tail_parts = (tail or "").strip().split(None, 1)
        extra_tail = tail_parts[1].strip() if len(tail_parts) > 1 else ""

    text = _rp_emit_action_text(
        action,
        int(actor_id),
        actor_tag,
        target_tag,
        extra_tail=extra_tail,
        comment_text=comment_text
    )

    try:
        sent = _REAL_BOT_REPLY_TO(
            message,
            text,
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        remember_reply_pair_for_autodelete(sent, message)
        _inc_personal_rp_use(action)
    except Exception:
        return False

    _rp_insert_event(action["trigger_key"], int(actor_id), int(target_id))
    return True

def handle_agents_panel_command(message):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not (is_creator(uid) or is_support(uid)):
        bot.reply_to(message, "📑 Эта команда доступна только технической поддержке.")
        return

    bot.reply_to(
        message,
        build_agents_panel_text(uid),
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_my_owner_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "my_owner":
        return
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not is_creator(uid):
        bot.reply_to(message, "📑 Только создатель бота может выдавать себе owner-права.")
        return

    if is_owner(uid):
        bot.reply_to(message, "📑 У вас уже есть owner-права.")
        return

    add_bot_owner(uid, uid)
    bot.reply_to(message, "✅ Вы выдали себе owner-права.")

def handle_my_owner_remove_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "my_owner_remove":
        return
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not is_creator(uid):
        bot.reply_to(message, "📑 Только создатель бота может снимать с себя owner-права.")
        return

    if not is_owner(uid):
        bot.reply_to(message, "📑 У вас уже нет owner-прав.")
        return

    remove_bot_owner(uid)
    bot.reply_to(message, "✅ Вы сняли с себя owner-права.")

def handle_owner_remove_command(message, parsed: Parsed):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not can_manage_owners(uid):
        bot.reply_to(message, "📑 Только создатель бота может снимать owner-права.")
        return

    target_id = resolve_target_id((parsed.args or "").strip())
    if target_id is None:
        return

    current_creator_id = int(get_current_creator_id())
    if int(target_id) == current_creator_id:
        bot.reply_to(message, "📑 Нельзя снять owner-права с текущего создателя через /owner_remove. Используйте /my_owner_remove.")
        return

    if not is_owner(int(target_id)):
        bot.reply_to(message, f"📑 Пользователь <code>{int(target_id)}</code> не является старшим агентом.", parse_mode="HTML")
        return

    remove_bot_owner(int(target_id))
    bot.reply_to(message, f"✅ Пользователь <code>{int(target_id)}</code> больше не является старшим агентом.", parse_mode="HTML")

def handle_agent_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "agent":
        return
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not can_manage_agents(uid):
        bot.reply_to(message, "📑 Только старший агент может назначать агентов техподдержки.")
        return

    target_id = resolve_target_id((parsed.args or "").strip())
    if target_id is None:
        return

    current_creator_id = int(get_current_creator_id())
    if int(target_id) == current_creator_id:
        bot.reply_to(message, "📑 Создателя бота нельзя назначить агентом техподдержки.")
        return

    if is_owner(int(target_id)):
        bot.reply_to(message, "📑 Старшему агенту не нужно выдавать права агента техподдержки отдельно.")
        return

    if is_agent(int(target_id)):
        bot.reply_to(message, f"📑 Пользователь <code>{int(target_id)}</code> уже является агентом техподдержки.", parse_mode="HTML")
        return

    add_agent(int(target_id), uid)

    row = get_user_row(int(target_id))
    disp = display_name(row["first_name"] or "", row["last_name"] or "", row["username"] or "", int(target_id)) if row else str(int(target_id))
    un = (row["username"] or "") if row else ""
    bot.reply_to(
        message,
        f"✅ Пользователь <b>{tg_mention(int(target_id), disp, username=un)}</b> назначен агентом технической поддержки.",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_agent_remove_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "agent_remove":
        return
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not can_manage_agents(uid):
        bot.reply_to(message, "📑 Только старший агент может снимать права агента техподдержки.")
        return

    target_id = resolve_target_id((parsed.args or "").strip())
    if target_id is None:
        return

    current_creator_id = int(get_current_creator_id())
    if int(target_id) == current_creator_id:
        bot.reply_to(message, "📑 Нельзя снять права агента с текущего создателя бота.")
        return

    if is_owner(int(target_id)):
        bot.reply_to(message, "📑 У старшего агента нет отдельной агентской роли для снятия.")
        return

    if not is_agent(int(target_id)):
        bot.reply_to(message, f"📑 Пользователь <code>{int(target_id)}</code> не является агентом техподдержки.", parse_mode="HTML")
        return

    remove_agent(int(target_id))
    bot.reply_to(message, f"✅ Пользователь <code>{int(target_id)}</code> больше не является агентом техподдержки.", parse_mode="HTML")

def handle_edit_k_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_float_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите числовое значение коэффициента k.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Коэффициент k не может быть отрицательным.")
        return

    save_infect_formula_settings(val, INFECT_BOUND_BETA)
    bot.reply_to(
        message,
        f"✅ Коэффициент масштаба (k) изменён на <b>{str(INFECT_BOUND_K).replace('.', ',')}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_edit_b_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_float_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите числовое значение коэффициента β.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Коэффициент β не может быть отрицательным.")
        return

    save_infect_formula_settings(INFECT_BOUND_K, val)
    bot.reply_to(
        message,
        f"✅ Коэффициент искривления (β) изменён на <b>{str(INFECT_BOUND_BETA).replace('.', ',')}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_cof_inf_stats_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    bot.reply_to(
        message,
        render_cof_inf_stats_text(),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_cof_inf_stats()
    )

def handle_duel_cof_stats_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    bot.reply_to(
        message,
        render_duel_cof_stats_text(),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_duel_cof_stats()
    )

def handle_duel_cof_break_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_int_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите целое число для базового шанса сбивания.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Шанс сбивания не может быть отрицательным.")
        return

    save_duel_formula_settings(break_base_pct=int(val))
    bot.reply_to(
        message,
        f"✅ Базовый шанс сбивания изменён на <b>{_fmt_pct_text(float(DUEL_BREAK_BASE_PCT))}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_duel_cof_break_bon_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_int_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите целое число для бонуса сбивания.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Бонус сбивания не может быть отрицательным.")
        return

    save_duel_formula_settings(break_step_pct=int(val))
    bot.reply_to(
        message,
        f"✅ Бонус к сбиванию за 1 стак изменён на <b>{_fmt_pct_text(float(DUEL_BREAK_STEP_PCT))}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_duel_cof_aim_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_int_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите целое число для бонуса прицеливания.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Бонус прицеливания не может быть отрицательным.")
        return

    save_duel_formula_settings(aim_step_pct=int(val))
    bot.reply_to(
        message,
        f"✅ Бонус прицеливания за 1 стак изменён на <b>{_fmt_pct_text(float(DUEL_AIM_STEP_PCT))}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_duel_cof_base_pts_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_int_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите целое число для базового шанса попадания.")
        return
    if val < 0:
        bot.reply_to(message, "📑 Шанс попадания не может быть отрицательным.")
        return

    save_duel_formula_settings(base_hit_pct=int(val))
    bot.reply_to(
        message,
        f"✅ Базовый шанс попадания изменён на <b>{_fmt_pct_text(float(DUEL_BASE_HIT_PCT))}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_duel_rounds_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or not can_manage_support(int(message.from_user.id)):
        return

    val = _parse_edit_int_arg(parsed.args or "")
    if val is None:
        bot.reply_to(message, "📑 Укажите целое число количества раундов.")
        return
    if val <= 0:
        bot.reply_to(message, "📑 Количество раундов должно быть больше нуля.")
        return

    save_duel_formula_settings(rounds_value=int(val))
    bot.reply_to(
        message,
        f"✅ Количество раундов дуэли изменено на <b>{int(DUEL_MAX_TURNS)}</b>",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_admin_name_restriction_command(message, parsed: Parsed):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not is_support(uid):
        bot.reply_to(message, "📑 Эта команда доступна только агентам техподдержки")
        return

    first_line, _body = _timer_first_line_and_body(message.text or "")
    fl = first_line.strip()
    if fl.startswith("/") or fl.startswith("."):
        fl = fl[1:].strip()

    target_id, _target_user_obj, reason = _resolve_admin_target_and_reason(message, parsed)
    if target_id is None:
        return

    if parsed.cmd == "name_lock_user":
        locked = 1 if fl.startswith("-") or fl.lower().startswith("-user_name") else 0
        set_name_restriction(int(target_id), "user", locked, int(uid), reason)
        if locked == 1:
            clear_all_chat_user_names_for_user(int(target_id))
        bot.reply_to(
            message,
            f"✅ Пользователю <code>{int(target_id)}</code> {'запрещено' if locked == 1 else 'разрешено'} менять имя пользователя в чатах.",
            parse_mode="HTML"
        )
        return

    if parsed.cmd == "name_lock_lab":
        locked = 1 if fl.startswith("-") or fl.lower().startswith("-lab_name") else 0
        set_name_restriction(int(target_id), "lab", locked, int(uid), reason)
        bot.reply_to(
            message,
            f"✅ Пользователю <code>{int(target_id)}</code> {'запрещено' if locked == 1 else 'разрешено'} менять имя лаборатории.",
            parse_mode="HTML"
        )
        return

    if parsed.cmd == "name_lock_pat":
        locked = 1 if fl.startswith("-") or fl.lower().startswith("-pat_name") else 0
        set_name_restriction(int(target_id), "pat", locked, int(uid), reason)
        bot.reply_to(
            message,
            f"✅ Пользователю <code>{int(target_id)}</code> {'запрещено' if locked == 1 else 'разрешено'} менять имя патогена.",
            parse_mode="HTML"
        )
        return

    locked = 1 if fl.startswith("-") or fl.lower().startswith("-corp_name") else 0
    set_name_restriction(int(target_id), "corp", locked, int(uid), reason)
    if locked == 1:
        _reset_owned_corp_name_to_default(int(target_id))
    bot.reply_to(
        message,
        f"✅ Пользователю <code>{int(target_id)}</code> {'запрещено' if locked == 1 else 'разрешено'} менять название корпорации.",
        parse_mode="HTML"
    )

def handle_blacklist_command(message):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not is_support(uid):
        bot.reply_to(message, "📑 Эта команда доступна только агентам техподдержки")
        return

    text, rm = render_blacklist_text(1)
    bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)

def handle_users_list_command(message):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not is_support(uid):
        bot.reply_to(message, "📑 Эта команда доступна только агентам техподдержки")
        return

    text, rm = render_users_text(1)
    bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)

def handle_promo_generate_command(message):
    uid = int(message.from_user.id)
    if not can_manage_support(uid):
        return

    code = _promo_make_random_code()
    bonuses = []

    # 1-3 случайных бонуса
    choices = ["res", "mat", "points", "skill"]
    random.shuffle(choices)
    for kind in choices[: random.randint(1, 3)]:
        if kind == "res":
            bonuses.append({"kind": "res", "ref_code": "", "amount": random.choice([50, 100, 150, 250, 500])})
        elif kind == "mat":
            bonuses.append({"kind": "mat", "ref_code": "", "amount": random.choice([20, 50, 100, 200])})
        elif kind == "points":
            bonuses.append({"kind": "points", "ref_code": "", "amount": random.choice([1, 2, 3])})
        else:
            sk = random.choice(list(SKILLS.keys()))
            bonuses.append({"kind": "skill", "ref_code": sk, "amount": random.choice([1, 2])})

    ts = int(now_ts() + 7 * 86400)
    _promo_create(code, 0, ts, bonuses, uid)

    bonus_txt = "\n".join([_promo_bonus_to_text(b) for b in bonuses if _promo_bonus_to_text(b)])
    bot.reply_to(
        message,
        f"✅ Промокод создан:\n<code>{h(code)}</code>\nДействителен до <code>{h(_fmt_ts(ts))}</code>\n{bonus_txt}",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_promo_create_command(message):
    uid = int(message.from_user.id)
    if not can_manage_support(uid):
        return

    payload, err = _promo_parse_create_message(message.text or "")
    if not payload:
        bot.reply_to(message, err, parse_mode="HTML", disable_web_page_preview=True)
        return

    try:
        _promo_create(
            payload["code"],
            int(payload["is_permanent"]),
            int(payload["expires_ts"]),
            list(payload["bonuses"]),
            uid
        )
    except sqlite3.IntegrityError:
        bot.reply_to(message, "📑 Промокод с таким названием уже существует.")
        return

    bonus_txt = "\n".join([_promo_bonus_to_text(b) for b in payload["bonuses"] if _promo_bonus_to_text(b)])
    status = "постоянный" if int(payload["is_permanent"]) == 1 else f"до <code>{h(_fmt_ts(int(payload['expires_ts'])))}</code>"
    bot.reply_to(
        message,
        f"✅ Промокод <code>{h(payload['code'])}</code> создан.\nСтатус: {status}\n{bonus_txt}",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_promo_all_command(message):
    uid = int(message.from_user.id)
    if not can_manage_support(uid):
        return
    text, rm = render_promocode_list_text(1)
    bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)

def handle_promo_delete_command(message, parsed: Parsed):
    uid = int(message.from_user.id)
    if not can_manage_support(uid):
        return

    arg = (parsed.args or "").strip()
    if not arg:
        return

    rows = _promo_fetch_all_rows()
    promo_id = None
    if arg.isdigit():
        idx = int(arg)
        if 1 <= idx <= len(rows):
            promo_id = int(rows[idx - 1]["promo_id"])
    else:
        code_key = _promo_norm_code(arg)
        for r in rows:
            if _promo_norm_code(r["code"]) == code_key:
                promo_id = int(r["promo_id"])
                break

    if promo_id is None:
        bot.reply_to(message, "📑 Промокод не найден.")
        return

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute("DELETE FROM promo_bonuses WHERE promo_id=?", (promo_id,))
            c.execute("DELETE FROM promo_uses WHERE promo_id=?", (promo_id,))
            c.execute("DELETE FROM promo_codes WHERE promo_id=?", (promo_id,))
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    bot.reply_to(message, "✅ Промокод удалён.")

def handle_promo_use_command(message, parsed: Parsed):
    uid = int(message.from_user.id)
    code = (parsed.args or "").strip()
    if not code:
        return
    ok, txt = _promo_apply_to_user(code, uid)
    bot.reply_to(message, txt, parse_mode="HTML", disable_web_page_preview=True)

def handle_timer_commands(message, parsed: Parsed):
    uid = int(message.from_user.id)
    chat_id = int(message.chat.id)
    upsert_user(message.from_user)
    ensure_creator_is_support()

    if parsed.cmd == "timer_list":
        bot.reply_to(message, render_timer_list_text(uid), parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd == "timer_clear_all":
        db_exec("DELETE FROM user_timers WHERE user_id=?", (int(uid),), commit=True)
        bot.reply_to(message, "✅ Все ваши таймеры успешно удалены.")
        return

    if parsed.cmd == "timer_delete":
        arg = (parsed.args or "").strip()
        if not arg.isdigit():
            bot.reply_to(message, "📑 Укажите номер таймера из списка.")
            return

        idx = int(arg)
        rows = _timer_rows_for_user(uid)
        if idx < 1 or idx > len(rows):
            bot.reply_to(message, "📑 Таймер с таким номером не найден.")
            return

        timer_id = int(rows[idx - 1]["timer_id"])
        db_exec("DELETE FROM user_timers WHERE timer_id=? AND user_id=?", (timer_id, int(uid)), commit=True)
        bot.reply_to(message, "✅ Таймер успешно удалён.")
        return

    command_text = _timer_body_command(message.text or "")
    ok_cmd, cmd_err = _timer_validate_body_command(command_text)
    if not ok_cmd:
        bot.reply_to(message, cmd_err)
        return

    current_rows = _timer_rows_for_user(uid)
    if len(current_rows) >= 10:
        bot.reply_to(message, "📑 У вас уже установлено максимальное количество таймеров: 10.")
        return

    if parsed.cmd == "timer_add_rel":
        spec, err = _timer_parse_period_spec((parsed.args or "").strip())
        if not spec:
            bot.reply_to(message, err)
            return

        next_dt = _timer_apply_period(datetime.now(), spec)
        next_run_ts = int(next_dt.timestamp())
        _timer_create(uid, chat_id, next_run_ts, 0, {}, command_text)

        bot.reply_to(
            message,
            f"✅ Таймер создан.\nСработает: <code>{h(_fmt_ts(next_run_ts))}</code>\nПериод: {_timer_spec_to_text(spec)}",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "timer_add_cycle":
        cycle_rows = db_all(
            "SELECT timer_id FROM user_timers WHERE user_id=? AND is_cycle=1 ORDER BY timer_id ASC",
            (int(uid),)
        ) or []
        if len(cycle_rows) >= 2:
            bot.reply_to(message, "📑 У вас уже установлено максимальное количество циклических таймеров: 2.")
            return

        runs_total, spec, err = _timer_parse_cycle_args((parsed.args or "").strip())
        if not spec:
            bot.reply_to(message, err, parse_mode="HTML", disable_web_page_preview=True)
            return

        next_dt = _timer_apply_period(datetime.now(), spec)
        next_run_ts = int(next_dt.timestamp())
        _timer_create(uid, chat_id, next_run_ts, 1, spec, command_text, cycle_total=int(runs_total), cycle_left=int(runs_total))

        bot.reply_to(
            message,
            f"✅ Циклический таймер создан.\n"
            f"Первое срабатывание: <code>{h(_fmt_ts(next_run_ts))}</code>\n"
            f"Период: {_timer_spec_to_text(spec)}\n"
            f"Срабатываний: <b>{int(runs_total)}</b>",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "timer_add_abs":
        ts, err = _timer_parse_absolute_spec((parsed.args or "").strip())
        if ts is None:
            bot.reply_to(message, err, parse_mode="HTML", disable_web_page_preview=True)
            return

        _timer_create(uid, chat_id, int(ts), 0, {}, command_text)
        bot.reply_to(
            message,
            f"✅ Таймер создан на <code>{h(_fmt_ts(int(ts)))}</code>",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

def handle_chat_autodelete_commands(message, parsed: Parsed):
    if message.chat.type not in ("group", "supergroup"):
        bot.reply_to(message, "📑 Эта команда работает только в групповом чате.")
        return

    chat_id = int(message.chat.id)
    uid = int(message.from_user.id)

    if not is_group_admin(uid, chat_id):
        bot.reply_to(message, "📑 Эта команда доступна только администраторам этого чата.")
        return

    if parsed.cmd == "chat_autodel_status":
        title = getattr(message.chat, "title", None) or "чат"
        bot.reply_to(
            message,
            render_auto_delete_status(chat_id, title),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "chat_autodel_off":
        forget_chat_auto_delete(chat_id)
        bot.reply_to(message, "✅ Авто-удаление сообщений для этого чата отключено.")
        return

    spec, err = _timer_parse_period_spec((parsed.args or "").strip())
    if not spec:
        bot.reply_to(message, err)
        return

    ttl = (
        int(spec.get("months", 0) or 0) * 30 * 86400
        + int(spec.get("weeks", 0) or 0) * 7 * 86400
        + int(spec.get("days", 0) or 0) * 86400
        + int(spec.get("hours", 0) or 0) * 3600
        + int(spec.get("minutes", 0) or 0) * 60
    )

    if ttl < 60:
        bot.reply_to(message, "📑 Минимальный период авто-удаления — 1 минута.")
        return

    if ttl > TIMER_MAX_SECONDS:
        bot.reply_to(message, "📑 Максимальный срок авто-удаления — один год.")
        return

    set_chat_auto_delete_ttl(chat_id, ttl, uid)
    run_chat_autodelete_once(chat_id)

    bot.reply_to(
        message,
        f"✅ Авто-удаление сообщений включено.\n⌛ {_format_duration(ttl)}",
        disable_web_page_preview=True
    )

# RESOLVE TARGETS
def _resolve_known_target_token(token: str) -> Optional[int]:
    if not token:
        return None
    s = token.strip()

    def _user_exists(uid: int) -> bool:
        return bool(db_one("SELECT 1 FROM users WHERE user_id=? LIMIT 1", (int(uid),)))

    m = re.search(r"tg://openmessage\?user_id=(\d+)", s, flags=re.IGNORECASE)
    if m:
        uid = int(m.group(1))
        return uid if _user_exists(uid) else None

    m = re.search(r"tg://user\?id=(\d+)", s, flags=re.IGNORECASE)
    if m:
        uid = int(m.group(1))
        return uid if _user_exists(uid) else None

    if re.fullmatch(r"\d+", s):
        uid = int(s)
        return uid if _user_exists(uid) else None

    uname = _extract_public_username_token(s)
    if uname:
        return find_user_id_by_username("@" + uname)

    m = re.search(r"@([A-Za-z0-9_]{3,64})", s)
    if m:
        return find_user_id_by_username("@" + m.group(1))

    return None

def resolve_target_id(token: str) -> Optional[int]:
    """/owner target: @username | tg://user?id=... | tg://openmessage?user_id=... | user_id | текст с упоминанием."""
    return _resolve_single_target_from_text(token or "", _resolve_known_target_token)

# LAB TEXT
def default_lab_name(user_row: Optional[sqlite3.Row], user_id: int) -> str:
    if user_row:
        disp = display_name(
            user_row["first_name"] or "",
            user_row["last_name"] or "",
            user_row["username"] or "",
            int(user_id),
        )
        return f"им. {disp}"
    return f"им. {user_id}"

def render_lab(user_id: int) -> str:
    lab = get_lab(user_id)
    u = get_user_row(user_id)

    lab_name = (lab["lab_name"] or "").strip()
    if not lab_name:
        lab_name = default_lab_name(u, user_id)

    pathogen_name = (lab["pathogen_name"] or "").strip() or "неизвестный патоген"
    corp_name = (lab["corp_name"] or "").strip()
    corp_line = ""
    try:
        corp_id = int(lab["corp_id"] or 0)
    except Exception:
        corp_id = 0
    if corp_id > 0:
        corp_row = corp_by_id(corp_id)
        if corp_row:
            corp_line = corp_clickable_name(corp_row)

    leader_name = display_name(
        (u["first_name"] or "") if u else "",
        (u["last_name"] or "") if u else "",
        (u["username"] or "") if u else "",
        int(user_id),
    )
    leader_un = (u["username"] or "") if u else ""
    leader = tg_mention(int(user_id), leader_name, username=leader_un)

    lines = []
    lines.append(f'🔬 Досье лаборатории <b>{h(lab_name)}</b>:')
    lines.append(f'Руководитель: {leader}')
    if corp_line:
        lines.append(f'🏢 Корпорация: <b>{corp_line}</b>')
    elif corp_name:
        lines.append(f'🏢 Корпорация: <b>{h(corp_name)}</b>')
    lines.append("")
    lines.append("<i>ОСНОВНАЯ ИНФОРМАЦИЯ:</i>")
    lines.append(f'🏷 Имя патогена: {h(pathogen_name)}')
    lines.append(f'🧪 Готовых патогенов: {lab["ready_pathogens"]} из {lab["total_pathogens"]}')
    npi = int(lab["next_pathogen_in"] or 0)
    if npi > 0:
        lines.append(f'⏱️ Новый патоген через {_format_hms(npi)}')
    else:
        lines.append('⏱️ Достигнут лимит производства')
    lines.append("")
    lines.append(f'💉 Готовых вакцин: {lab["ready_vaccines"]} из {lab["total_vaccines"]}')
    nvi = int(lab["next_vaccine_in"] or 0)
    if nvi > 0:
        lines.append(f'⏱️ Новая вакцина через {_format_hms(nvi)}')
    else:
        lines.append('⏱️ Достигнут лимит производства')
    lines.append("")
    qual = (
        int(_rget(lab, "total_pathogens", 1) or 1)
        + int(_rget(lab, "total_vaccines", 1) or 1)
        + int(_rget(lab, "synthesis", 1) or 1)
        + int(_rget(lab, "acceleration", 1) or 1)
    ) // 4
    lines.append(f'👨‍🔬 Квалификация учёных: {qual} ур')
    sec = (
        int(_rget(lab, "reaction", 1) or 1)
        + int(_rget(lab, "ids", 1) or 1)
        + int(_rget(lab, "ips", 1) or 1)
    ) // 3
    lines.append(f'🕵️‍♂️ Служба безопасности: {sec} ур')     
    lines.append("")
    lines.append("<i>НАВЫКИ:</i>")
    lines.append(f'🦠 Заразность: {lab["infectivity"]} ур')
    lines.append(f'☠️ Летальность: {lab["lethality"]} ур')
    lines.append(f'🧿 Тяжесть: {lab["heaviness"]} ур')
    lines.append(f'🛡 Иммунитет: {lab["immunity"]} ур')
    lines.append("")
    lines.append("<i>СТАТИСТИКА:</i>")
    bio_exp = int(lab["bio_exp"] or 0)
    bio_res = int(lab["all_bio_res"] or 0)
    lines.append(f'☣️ Био-опыт: {_fmt_k(bio_exp)}')
    lines.append(f'🧬 Био-ресурс: {_fmt_k(bio_res)}')
    succ = int(lab["successful_ops"] or 0)
    tot = int(lab["ops_total"] or 0)
    pct = int(round((succ / tot) * 100)) if tot > 0 else 0
    lines.append(f'⛑️ Спецопераций: {succ} из {tot} ({pct}%)')
    prev = int(lab["prevented_ops"] or 0)
    dft = int(lab["defended_total"] or 0)
    pct2 = int(round((prev / dft) * 100)) if dft > 0 else 0
    lines.append(f"🥽 Предотвращены: {prev} из {dft} ({pct2}%)")
    lines.append("")
    lines.append(f'🤧 Заражённых: {lab["infected_total"]}')
    lines.append(f'🤒 Своих болезней: {lab["diseases_total"]}')
    now = now_ts()
    fever_until = int(lab["fever_until_ts"] or 0)
    if fever_until > now:
        left = fever_until - now
        fp = (lab["fever_pathogen"] or "").strip()
        lines.append(f'🌡️ Руководитель в состоянии горячки, вызванной болезнью {_pat_for_fever(fp)}, ещё {_format_hms(left)}')   
    return "\n".join(lines)

def _lab_owner_bundle(owner_id: int):
    lab = get_lab(owner_id)
    u = get_user_row(owner_id)

    lab_name = (lab["lab_name"] or "").strip()
    if not lab_name:
        lab_name = default_lab_name(u, owner_id)

    corp_name = (lab["corp_name"] or "").strip()

    leader_name = display_name(
        (u["first_name"] or "") if u else "",
        (u["last_name"] or "") if u else "",
        (u["username"] or "") if u else "",
        int(owner_id),
    )
    leader_un = (u["username"] or "") if u else ""
    leader = tg_mention(int(owner_id), leader_name, username=leader_un)
    return lab, lab_name, corp_name, leader

def _labui_data(owner_id: int, view: str) -> str:
    return f"{LABUI_TAG}:{int(owner_id)}:{view}"

def _labui_parse(data: str):
    try:
        parts = (data or "").split(":")
        if len(parts) != 3:
            return None, None
        if parts[0] != LABUI_TAG:
            return None, None
        oid = int(parts[1])
        v = parts[2]
        return oid, v
    except Exception:
        return None, None

def kb_lab_dossier(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_icon_only("👨‍🔬", callback_data=_labui_data(owner_id, "R"), style="primary"),
        _ikb_premium_icon_only("🕵️‍♂️", callback_data=_labui_data(owner_id, "S"), style="primary"),
    )
    kb.row(
        _ikb_premium_icon_only("🦠", callback_data=_upg_cb("P", owner_id, "INF", 1, "D")),
        _ikb_premium_icon_only("☠️", callback_data=_upg_cb("P", owner_id, "LET", 1, "D")),
        _ikb_premium_icon_only("🧿", callback_data=_upg_cb("P", owner_id, "HEA", 1, "D")),
        _ikb_premium_icon_only("🛡", callback_data=_upg_cb("P", owner_id, "IMM", 1, "D")),
    )
    kb.row(
        _ikb_premium_lead("🤧", "Заражённые", callback_data=_labui_data(owner_id, "I"), style="primary"),
        _ikb_premium_lead("🤒", "Ваши болезни", callback_data=_labui_data(owner_id, "B"), style="primary"),
    )
    return kb

def kb_lab_dev(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_icon_only("🧪", callback_data=_upg_cb("P", owner_id, "PAT", 1, "D")),
        _ikb_premium_icon_only("💉", callback_data=_upg_cb("P", owner_id, "VAC", 1, "D")),
        _ikb_premium_icon_only("⚗️", callback_data=_upg_cb("P", owner_id, "SYN", 1, "D")),
        _ikb_premium_icon_only("🧫", callback_data=_upg_cb("P", owner_id, "ACC", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"))
    return kb

def kb_lab_sec(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_icon_only("👮", callback_data=_upg_cb("P", owner_id, "REA", 1, "D")),
        _ikb_premium_icon_only("🛰️", callback_data=_upg_cb("P", owner_id, "IDS", 1, "D")),
        _ikb_premium_icon_only("📟", callback_data=_upg_cb("P", owner_id, "IPS", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"))
    return kb

def kb_lab_infected(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_lead("🤒", "Ваши болезни", callback_data=_labui_data(owner_id, "B"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"),
    )
    return kb

def kb_lab_diseases(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_lead("🤧", "Заражённые", callback_data=_labui_data(owner_id, "I"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"),
    )
    return kb

def kb_lab_dossier_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("👨‍🔬", callback_data=_labui_data(owner_id, "R")),
        InlineKeyboardButton("🕵️‍♂️", callback_data=_labui_data(owner_id, "S")),
    )
    kb.row(
        InlineKeyboardButton("🦠", callback_data=_upg_cb("P", owner_id, "INF", 1, "D")),
        InlineKeyboardButton("☠️", callback_data=_upg_cb("P", owner_id, "LET", 1, "D")),
        InlineKeyboardButton("🧿", callback_data=_upg_cb("P", owner_id, "HEA", 1, "D")),
        InlineKeyboardButton("🛡️", callback_data=_upg_cb("P", owner_id, "IMM", 1, "D")),
    )
    kb.row(
        InlineKeyboardButton("🤧 Заражённые", callback_data=_labui_data(owner_id, "I"), style="primary"),
        InlineKeyboardButton("🤒 Ваши болезни", callback_data=_labui_data(owner_id, "B"), style="primary"),
    )
    return kb

def kb_lab_dev_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🧪", callback_data=_upg_cb("P", owner_id, "PAT", 1, "D")),
        InlineKeyboardButton("💉", callback_data=_upg_cb("P", owner_id, "VAC", 1, "D")),
        InlineKeyboardButton("⚗️", callback_data=_upg_cb("P", owner_id, "SYN", 1, "D")),
        InlineKeyboardButton("🧫", callback_data=_upg_cb("P", owner_id, "ACC", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"))
    return kb

def kb_lab_sec_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("👮", callback_data=_upg_cb("P", owner_id, "REA", 1, "D")),
        InlineKeyboardButton("🛰️", callback_data=_upg_cb("P", owner_id, "IDS", 1, "D")),
        InlineKeyboardButton("📟", callback_data=_upg_cb("P", owner_id, "IPS", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"))
    return kb

def kb_lab_infected_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🤒 Ваши болезни", callback_data=_labui_data(owner_id, "B"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"),
    )
    return kb

def kb_lab_diseases_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🤧 Заражённые", callback_data=_labui_data(owner_id, "I"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D"), style="primary"),
    )
    return kb

def render_lab_dev(owner_id: int) -> str:
    lab, lab_name, corp_name, leader = _lab_owner_bundle(owner_id)
    lines = []
    lines.append(f'🏥 Отдел разработок лаборатории <b>{h(lab_name)}</b>:')
    lines.append(f'Руководитель: {leader}')
    corp_line = ""
    try:
        corp_id = int(lab["corp_id"] or 0)
    except Exception:
        corp_id = 0
    if corp_id > 0:
        corp_row = corp_by_id(corp_id)
        if corp_row:
            corp_line = corp_clickable_name(corp_row)

    if corp_line:
        lines.append(f'🏢 Корпорация: <b>{corp_line}</b>')
    elif corp_name:
        lines.append(f'🏢 Корпорация: <b>{h(corp_name)}</b>')
    qual = (
        int(_rget(lab, "total_pathogens", 1) or 1)
        + int(_rget(lab, "total_vaccines", 1) or 1)
        + int(_rget(lab, "synthesis", 1) or 1)
        + int(_rget(lab, "acceleration", 1) or 1)
    ) // 4   
    lines.append(f'👨‍🔬 Квалификация учёных: {qual} ур')
    lines.append("")
    lines.append("<i>ХАРАКТЕРИСТИКИ:</i>")
    lines.append(f'🧪 Количество патогенов: {lab["total_pathogens"]}')
    lines.append(f'💉 Количество вакцин: {lab["total_vaccines"]}')
    lines.append(f'⚗️ Синтез: {_rget(lab,"synthesis",1)} ур')
    lines.append(f'🧫 Ускоренное производство: {_rget(lab,"acceleration",1)} ур')
    return "\n".join(lines)

def render_lab_sec(owner_id: int) -> str:
    lab, lab_name, corp_name, leader = _lab_owner_bundle(owner_id)
    lines = []
    lines.append(f'🏣 Отдел безопасности лаборатории <b>{h(lab_name)}</b>:')
    lines.append(f'Руководитель: {leader}')
    corp_line = ""
    try:
        corp_id = int(lab["corp_id"] or 0)
    except Exception:
        corp_id = 0
    if corp_id > 0:
        corp_row = corp_by_id(corp_id)
        if corp_row:
            corp_line = corp_clickable_name(corp_row)
    if corp_line:
        lines.append(f'🏢 Корпорация: <b>{corp_line}</b>')
    elif corp_name:
        lines.append(f'🏢 Корпорация: <b>{h(corp_name)}</b>')
    sec = (
        int(_rget(lab, "reaction", 1) or 1)
        + int(_rget(lab, "ids", 1) or 1)
        + int(_rget(lab, "ips", 1) or 1)
    ) // 3
    lines.append(f'🕵️‍♂️ Служба безопасности: {sec} ур')
    lines.append("")
    lines.append("<i>ХАРАКТЕРИСТИКИ:</i>")
    lines.append(f'👮 Группа быстрого реагирования: {_rget(lab, "reaction", 1)} ур')
    lines.append(f'🛰️ Система обнаружения вторжений: {_rget(lab, "ids", 1)} ур')
    lines.append(f'📟 Система предотвращения вторжений: {_rget(lab, "ips", 1)} ур')
    return "\n".join(lines)

def render_lab_infected_list(owner_id: int) -> str:
    rows = db_all(
        "SELECT target_id, add_bio_res, end_ts, start_ts FROM infections "
        "WHERE attacker_id=? ORDER BY start_ts DESC LIMIT 30",
        (int(owner_id),)
    ) or []

    agg = db_one(
        "SELECT "
        "COUNT(*) AS total_cnt, "
        "COALESCE(SUM(add_bio_res),0) AS total_daily_res, "
        "COALESCE(SUM(CASE WHEN start_ts>=? THEN 1 ELSE 0 END),0) AS last24_cnt "
        "FROM infections WHERE attacker_id=?",
        (int(now_ts() - 86400), int(owner_id))
    )

    total_cnt = int(agg["total_cnt"] or 0) if agg else 0
    total_daily_res = int(agg["total_daily_res"] or 0) if agg else 0
    last24_cnt = int(agg["last24_cnt"] or 0) if agg else 0

    lines = ["🔬 СПИСОК ЗАРАЖЕННЫХ ВАШИМ ПАТОГЕНОМ:"]
    if not rows:
        lines.append("<blockquote>Нет заражённых.</blockquote>")
        lines.append("")
        lines.append(f"Общее число заражённых: 👥 {total_cnt} (+{last24_cnt})")
        res_word = _ru_form(total_daily_res, 'био-ресурс', 'био-ресурса', 'био-ресурсов')
        lines.append(f"🧬 +{total_daily_res} {res_word}")
        return "\n".join(lines)

    items = []
    for i, r in enumerate(rows, 1):
        tid = int(r["target_id"])
        add = 1 if tid < 0 else int(r["add_bio_res"] or 0)
        end_ts = int(r["end_ts"] or 0)
        until = _fmt_date_ddmmyy(end_ts)

        name = public_user_tag(int(tid))
        res_word = _ru_form(int(add), "био-ресурс", "био-ресурса", "био-ресурсов")
        items.append(f"{i}. {name} | 🧬 {int(add)} {res_word} | до {until}")

    lines.append("<blockquote expandable>")
    lines.extend(items)
    lines.append("</blockquote>")
    lines.append("")
    lines.append(f"Общее число заражённых: 👥 {total_cnt} (+{last24_cnt})")
    total_res_word = _ru_form(total_daily_res, "био-ресурс", "био-ресурса", "био-ресурсов")
    lines.append(f"🧬 +{total_daily_res} {total_res_word}")
    return "\n".join(lines)

def render_lab_diseases_list(owner_id: int) -> str:
    rows = db_all(
        "SELECT i.attacker_id, i.end_ts, i.start_ts, COALESCE(i.known_to_target,0) AS known_to_target, "
        "COALESCE(la.pathogen_name,'') AS current_pathogen_name, "
        "u.username, u.first_name, u.last_name "
        "FROM infections i "
        "LEFT JOIN labs la ON la.user_id=i.attacker_id "
        "LEFT JOIN users u ON u.user_id=i.attacker_id "
        "WHERE i.target_id=? "
        "ORDER BY i.start_ts DESC LIMIT 30",
        (int(owner_id),)
    ) or []

    lines = ["🔬 СПИСОК ВАШИХ БОЛЕЗНЕЙ:"]
    if not rows:
        lines.append("<blockquote>Нет активных болезней.</blockquote>")
        return "\n".join(lines)

    items = []
    for i, r in enumerate(rows, 1):
        attacker_id = int(r["attacker_id"] or 0)
        known_to_target = int(r["known_to_target"] or 0)
        pname = (r["current_pathogen_name"] or "").strip()
        disease = f"«{h(pname)}»" if pname else "неизвестный патоген"
        until = _fmt_date_ddmmyy(int(r["end_ts"] or 0))

        if attacker_id != 0 and known_to_target == 1:
            owner_un = (r["username"] or "").strip()
            owner_disp = display_name(
                r["first_name"] or "",
                r["last_name"] or "",
                owner_un,
                attacker_id
            )
            inf_by = tg_mention(attacker_id, owner_disp, username=owner_un)
        else:
            inf_by = "неизвестный пользователь"

        items.append(f"{i}. {inf_by} | {disease} | до {until}")

    lines.append("<blockquote expandable>")
    lines.extend(items)
    lines.append("</blockquote>")
    return "\n".join(lines)

# форматы времени
def _ru_form(n: int, one: str, few: str, many: str) -> str:
    """1 -> one, 2-4 -> few, остальное -> many (с исключением 11-14)."""
    n = abs(int(n))
    n10 = n % 10
    n100 = n % 100
    if n100 in (11, 12, 13, 14):
        return many
    if n10 == 1:
        return one
    if n10 in (2, 3, 4):
        return few
    return many

def _ru_unit(n: int, one: str, few: str, many: str) -> str:
    n = abs(int(n))
    n10 = n % 10
    n100 = n % 100
    if n100 in (11, 12, 13, 14):
        return many
    if n10 == 1:
        return one
    if n10 in (2, 3, 4):
        return few
    return many

def _fmt_bio_res_after_po(n: int) -> str:
    n = int(n)
    w = _ru_unit(n, "био-ресурсу", "био-ресурса", "био-ресурсов")
    return f"{n} {w}"

def _format_hm_from_seconds(seconds: int) -> str:
    """Часы+минуты, без секунд (для строки 'Горячка на ...')."""
    seconds = max(0, int(seconds))
    total_min = max(1, (seconds + 59) // 60)
    h = total_min // 60
    m = total_min % 60
    parts = []
    if h > 0:
        parts.append(f"{h} {_ru_unit(h, 'час', 'часа', 'часов')}")
    parts.append(f"{m} {_ru_unit(m, 'минута', 'минуты', 'минут')}")
    return " ".join(parts)

def _format_days(n_days: int) -> str:
    d = max(0, int(n_days))
    return f"{d} {_ru_unit(d, 'день', 'дня', 'дней')}"

def _format_duration(seconds: int) -> str:
    seconds = max(0, int(seconds))
    m_total = (seconds + 59) // 60

    if m_total < 60:
        return f"{m_total} {_ru_unit(m_total, 'минута', 'минуты', 'минут')}"

    h = m_total // 60
    m = m_total % 60

    parts = [f"{h} {_ru_unit(h, 'час', 'часа', 'часов')}"]
    if m > 0:
        parts.append(f"{m} {_ru_unit(m, 'минута', 'минуты', 'минут')}")
    return " ".join(parts)

def _format_hms(seconds: int) -> str:
    seconds = max(0, int(seconds))
    h = seconds // 3600
    m = (seconds % 3600) // 60
    s = seconds % 60

    parts = []
    if h > 0:
        parts.append(f"{h} {_ru_unit(h, 'час', 'часа', 'часов')}")
    if m > 0:
        parts.append(f"{m} {_ru_unit(m, 'минута', 'минуты', 'минут')}")
    parts.append(f"{s} {_ru_unit(s, 'секунда', 'секунды', 'секунд')}")
    return " ".join(parts)

def _fmt_ts(ts: int) -> str:
    try:
        return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(ts)))
    except Exception:
        return str(ts)

def _fmt_date_ddmmyy(ts: int) -> str:
    try:
        return time.strftime("%d.%m.%y", time.localtime(int(ts)))
    except Exception:
        return "??.??.??"

TIMER_MAX_SECONDS = 366 * 24 * 3600
TIMER_PAGE_SIZE = 15

def _timer_first_line_and_body(text: str) -> tuple[str, str]:
    raw = (text or "").strip()
    first, _, body = raw.partition("\n")
    return first.strip(), body.strip()

def _timer_parse_reason_from_message(text: str) -> str:
    _first, body = _timer_first_line_and_body(text)
    body = (body or "").strip()
    if not body:
        return ""
    return body[:50]

def _timer_period_unit_key(unit_raw: str) -> str:
    u = (unit_raw or "").strip().lower()

    if u in ("мин", "минута", "минуты", "минут", "минуту"):
        return "minutes"

    if u in ("час", "часа", "часов"):
        return "hours"

    if u in ("день", "дня", "дней"):
        return "days"

    if u in ("неделя", "недели", "недель", "неделю"):
        return "weeks"

    if u in ("месяц", "месяца", "месяцев", "мес"):
        return "months"

    return ""

def _timer_parse_period_spec(text: str) -> tuple[Optional[dict], str]:
    s = (text or "").strip().lower()
    if not s:
        return None, "📑 Укажите период таймера."

    pattern = re.compile(
        r"(?P<num>\d+)?\s*(?P<unit>"
        r"минуту|минуты|минута|минут|мин|"
        r"часов|часа|час|"
        r"неделю|недели|неделя|недель|"
        r"дней|дня|день|"
        r"месяцев|месяца|месяц|мес"
        r")",
        flags=re.IGNORECASE
    )

    pos = 0
    spec = {"months": 0, "weeks": 0, "days": 0, "hours": 0, "minutes": 0}
    found = False

    for m in pattern.finditer(s):
        gap = s[pos:m.start()]
        if gap.strip():
            return None, "📑 Неверный формат периода таймера."

        num = int(m.group("num") or 1)
        if num <= 0:
            return None, "📑 Значение периода должно быть больше нуля."

        key = _timer_period_unit_key(m.group("unit"))
        if not key:
            return None, "📑 Неверный формат периода таймера."

        spec[key] += num
        pos = m.end()
        found = True

    if not found:
        return None, "📑 Неверный формат периода таймера."

    if s[pos:].strip():
        return None, "📑 Неверный формат периода таймера."

    approx = (
        spec["months"] * 30 * 86400
        + spec["weeks"] * 7 * 86400
        + spec["days"] * 86400
        + spec["hours"] * 3600
        + spec["minutes"] * 60
    )

    if approx <= 0:
        return None, "📑 Период таймера должен быть больше нуля."
    if approx > TIMER_MAX_SECONDS:
        return None, "📑 Максимальный срок таймера — один год."

    return spec, ""

def _timer_spec_to_text(spec: dict) -> str:
    parts = []

    hours = int(spec.get("hours", 0) or 0)
    minutes = int(spec.get("minutes", 0) or 0)
    days = int(spec.get("days", 0) or 0)
    weeks = int(spec.get("weeks", 0) or 0)
    months = int(spec.get("months", 0) or 0)

    if hours > 0:
        parts.append(f"{hours} {_ru_form(hours, 'час', 'часа', 'часов')}")
    if minutes > 0:
        parts.append(f"{minutes} {_ru_form(minutes, 'минута', 'минуты', 'минут')}")
    if days > 0:
        parts.append(f"{days} {_ru_form(days, 'день', 'дня', 'дней')}")
    if weeks > 0:
        parts.append(f"{weeks} {_ru_form(weeks, 'неделя', 'недели', 'недель')}")
    if months > 0:
        parts.append(f"{months} {_ru_form(months, 'месяц', 'месяца', 'месяцев')}")

    return " ".join(parts) if parts else "0 минут"

# Автоудаление
def get_bot_chat_admin_rights(chat_id: int) -> dict:
    out = {
        "is_admin": False,
        "status": "",
        "can_delete_messages": False,
        "can_restrict_members": False,
        "can_pin_messages": False,
        "can_invite_users": False,
        "can_manage_chat": False,
        "can_change_info": False,
    }

    try:
        bot_id = int(BOT_ID or 0)
        if bot_id <= 0:
            me = bot.get_me()
            bot_id = int(getattr(me, "id", 0) or 0)

        if bot_id <= 0:
            return out

        cm = bot.get_chat_member(int(chat_id), int(bot_id))
        st = (getattr(cm, "status", "") or "").lower()
        is_admin = st in ("administrator", "creator")

        out["status"] = st
        out["is_admin"] = is_admin
        out["can_delete_messages"] = (st == "creator") or bool(getattr(cm, "can_delete_messages", False))
        out["can_restrict_members"] = (st == "creator") or bool(getattr(cm, "can_restrict_members", False))
        out["can_pin_messages"] = (st == "creator") or bool(getattr(cm, "can_pin_messages", False))
        out["can_invite_users"] = (st == "creator") or bool(getattr(cm, "can_invite_users", False))
        out["can_manage_chat"] = (st == "creator") or bool(getattr(cm, "can_manage_chat", False))
        out["can_change_info"] = (st == "creator") or bool(getattr(cm, "can_change_info", False))
    except Exception:
        pass

    return out

def bot_can_delete_chat_messages(chat_id: int) -> bool:
    return bool(get_bot_chat_admin_rights(int(chat_id)).get("can_delete_messages", False))

def is_group_admin(user_id: int, chat_id: int) -> bool:
    try:
        cm = bot.get_chat_member(int(chat_id), int(user_id))
        st = (getattr(cm, "status", "") or "").lower()
        return st in ("administrator", "creator")
    except Exception:
        return False

def get_chat_auto_delete_ttl(chat_id: int) -> int:
    row = db_one("SELECT COALESCE(ttl_seconds,0) AS t FROM chat_auto_delete WHERE chat_id=? LIMIT 1", (int(chat_id),))
    return int(row["t"] or 0) if row else 0

def set_chat_auto_delete_ttl(chat_id: int, ttl_seconds: int, by_user_id: int):
    db_exec(
        "INSERT INTO chat_auto_delete(chat_id, ttl_seconds, updated_by, updated_at) VALUES (?,?,?,?) "
        "ON CONFLICT(chat_id) DO UPDATE SET ttl_seconds=excluded.ttl_seconds, updated_by=excluded.updated_by, updated_at=excluded.updated_at",
        (int(chat_id), int(ttl_seconds), int(by_user_id), int(now_ts())),
        commit=True
    )

def forget_chat_auto_delete(chat_id: int):
    db_exec("DELETE FROM chat_auto_delete WHERE chat_id=?", (int(chat_id),), commit=True)

def _is_text_command_message_for_autodelete(message) -> bool:
    txt = ((getattr(message, "text", None) or getattr(message, "caption", None) or "")).strip()
    if not txt:
        return False

    try:
        if parse_message_as_command(txt) is not None:
            return True
    except Exception:
        pass

    try:
        actor = getattr(message, "from_user", None)
        actor_id = int(getattr(actor, "id", 0) or 0) if actor else 0
        action, _tail, _comment = _parse_rp_message(txt, actor_id)
        if action:
            return True
    except Exception:
        pass

    return False

def remember_bot_message_for_autodelete(msg):
    try:
        if not msg:
            return
        chat = getattr(msg, "chat", None)
        if not chat:
            return
        chat_type = (getattr(chat, "type", "") or "").lower()
        if chat_type not in ("group", "supergroup"):
            return
        chat_id = int(chat.id)
        ttl = get_chat_auto_delete_ttl(chat_id)
        if ttl <= 0:
            return
        db_exec(
            "INSERT OR REPLACE INTO bot_sent_messages(chat_id, message_id, sent_at) VALUES (?,?,?)",
            (chat_id, int(msg.message_id), int(now_ts())),
            commit=True
        )
    except Exception:
        pass

def remember_user_trigger_message_for_autodelete(message):
    try:
        if not message:
            return

        chat = getattr(message, "chat", None)
        if not chat:
            return

        chat_type = (getattr(chat, "type", "") or "").lower()
        if chat_type not in ("group", "supergroup"):
            return

        chat_id = int(chat.id)
        ttl = get_chat_auto_delete_ttl(chat_id)
        if ttl <= 0:
            return

        if not bot_can_delete_chat_messages(chat_id):
            return

        if not _is_text_command_message_for_autodelete(message):
            return

        mid = int(getattr(message, "message_id", 0) or 0)
        if mid <= 0:
            return

        db_exec(
            "INSERT OR REPLACE INTO bot_sent_messages(chat_id, message_id, sent_at) VALUES (?,?,?)",
            (chat_id, mid, int(now_ts())),
            commit=True
        )
    except Exception:
        pass

def remember_reply_pair_for_autodelete(sent_msg=None, trigger_message=None):
    """
    sent_msg — сообщение, которое отправил бот
    trigger_message — исходное сообщение пользователя, вызвавшее реакцию бота
    """
    try:
        if sent_msg is not None:
            remember_bot_message_for_autodelete(sent_msg)
    except Exception:
        pass

    try:
        if trigger_message is not None:
            remember_user_trigger_message_for_autodelete(trigger_message)
    except Exception:
        pass

def run_chat_autodelete_once(chat_id: Optional[int] = None):
    now = int(now_ts())

    if chat_id is not None:
        settings = db_all(
            "SELECT chat_id, ttl_seconds FROM chat_auto_delete WHERE chat_id=? AND COALESCE(ttl_seconds,0)>0",
            (int(chat_id),)
        ) or []
    else:
        settings = db_all(
            "SELECT chat_id, ttl_seconds FROM chat_auto_delete WHERE COALESCE(ttl_seconds,0)>0"
        ) or []

    for s in settings:
        cid = int(s["chat_id"])
        ttl = int(s["ttl_seconds"] or 0)
        if ttl <= 0:
            continue

        rows = db_all(
            "SELECT message_id, sent_at FROM bot_sent_messages WHERE chat_id=? AND sent_at<=? ORDER BY sent_at ASC LIMIT 100",
            (cid, int(now - ttl))
        ) or []

        for r in rows:
            mid = int(r["message_id"])
            try:
                bot.delete_message(cid, mid)
            except Exception:
                pass
            finally:
                db_exec("DELETE FROM bot_sent_messages WHERE chat_id=? AND message_id=?", (cid, mid), commit=True)

def render_auto_delete_status(chat_id: int, chat_title: str) -> str:
    ttl = get_chat_auto_delete_ttl(int(chat_id))
    if ttl > 0:
        val = f"⌛ {_format_duration(ttl)}"
    else:
        val = "❌ Отключено"

    rights = get_bot_chat_admin_rights(int(chat_id))
    if rights["can_delete_messages"]:
        rights_text = "🤖 Бот: администратор, удаление сообщений доступно"
    elif rights["is_admin"]:
        rights_text = "🤖 Бот: администратор, но без права удалять сообщения"
    else:
        rights_text = "🤖 Бот: не является администратором"

    return (
        f"🔏 Авто-удаление сообщений чата <b>{h(chat_title)}</b>\n"
        f"{val}\n"
        f"{rights_text}\n\n"
        f"💬 Чтобы изменить время, введите \"<code>Био +автоудаление</code>\" + период"
    )

# Таймеры
def _timer_spec_seconds_approx(spec: dict) -> int:
    return int(
        int(spec.get("months", 0) or 0) * 30 * 86400
        + int(spec.get("weeks", 0) or 0) * 7 * 86400
        + int(spec.get("days", 0) or 0) * 86400
        + int(spec.get("hours", 0) or 0) * 3600
        + int(spec.get("minutes", 0) or 0) * 60
    )

def _timer_parse_cycle_args(text: str) -> tuple[Optional[int], Optional[dict], str]:
    s = (text or "").strip()
    if not s:
        return None, None, "📑 Укажите число срабатываний и период циклического таймера."

    parts = s.split(None, 1)
    if len(parts) < 2 or not parts[0].isdigit():
        return None, None

    runs_total = int(parts[0])
    if runs_total < 2 or runs_total > 30:
        return None, None, "📑 Количество срабатываний циклического таймера должно быть от 2 до 30."

    spec, err = _timer_parse_period_spec(parts[1].strip())
    if not spec:
        return None, None, err

    if _timer_spec_seconds_approx(spec) < 600:
        return None, None, "📑 Минимальный период циклического таймера — 10 минут."

    return runs_total, spec, ""

def _timer_add_months(dt: datetime, months: int) -> datetime:
    if months <= 0:
        return dt

    month_index = (dt.month - 1) + int(months)
    year = dt.year + (month_index // 12)
    month = (month_index % 12) + 1
    day = min(dt.day, calendar.monthrange(year, month)[1])

    return dt.replace(year=year, month=month, day=day)

def _timer_apply_period(dt: datetime, spec: dict) -> datetime:
    out = dt
    out = _timer_add_months(out, int(spec.get("months", 0) or 0))
    out = out + timedelta(
        weeks=int(spec.get("weeks", 0) or 0),
        days=int(spec.get("days", 0) or 0),
        hours=int(spec.get("hours", 0) or 0),
        minutes=int(spec.get("minutes", 0) or 0),
    )
    return out

_TIMER_ABS_FORMATS_HELP = (
    "📋 Поддерживаемые форматы:\n"
    "<blockquote expandable>\n"
    "чч:мм:сс\n"
    "чч:мм\n"
    "чч\n"
    "дд.мм.гггг\n"
    "дд.мм\n"
    "дд\n"
    "чч:мм:сс дд.мм.гггг\n"
    "чч:мм:сс дд.мм\n"
    "чч:мм:сс дд\n"
    "чч:мм дд.мм.гггг\n"
    "чч:мм дд.мм\n"
    "чч:мм дд\n"
    "чч дд.мм.гггг\n"
    "чч дд.мм\n"
    "чч дд\n"
    "дд.мм.гггг чч:мм:сс\n"
    "дд.мм чч:мм:сс\n"
    "дд чч:мм:сс\n"
    "дд.мм.гггг чч:мм\n"
    "дд.мм чч:мм\n"
    "дд чч:мм\n"
    "дд.мм.гггг чч\n"
    "дд.мм чч\n"
    "дд чч\n"
    "</blockquote>"
)

def _timer_invalid_abs_error() -> str:
    return "📑 Неверный формат периода таймера.\n" + _TIMER_ABS_FORMATS_HELP

def _parse_time_token(tok: str):
    s = (tok or "").strip()
    if not s:
        return None
    if not re.fullmatch(r"\d{1,2}(:\d{1,2}){0,2}", s):
        return None

    parts = [int(x) for x in s.split(":")]
    if len(parts) == 1:
        hh, mm, ss = parts[0], 0, 0
    elif len(parts) == 2:
        hh, mm = parts
        ss = 0
    else:
        hh, mm, ss = parts

    if hh > 23 or mm > 59 or ss > 59:
        return None
    return hh, mm, ss

def _parse_date_token(tok: str):
    s = (tok or "").strip()
    if not s:
        return None

    if not re.fullmatch(r"\d{1,2}(\.\d{1,2}){0,1}(\.\d{2}|\.\d{4}){0,1}", s):
        return None

    parts = s.split(".")
    if len(parts) == 1:
        return {"day": int(parts[0]), "month": None, "year": None}

    if len(parts) == 2:
        return {"day": int(parts[0]), "month": int(parts[1]), "year": None}

    y_raw = parts[2].strip()
    y = int(y_raw)
    if len(y_raw) == 2:
        y += 2000

    return {"day": int(parts[0]), "month": int(parts[1]), "year": y}

def _next_valid_month_day_after(base_dt: datetime, day: int, month: int, hh: int, mm: int, ss: int):
    year = base_dt.year
    for plus_year in (0, 1):
        y = year + plus_year
        try:
            cand = datetime(y, month, day, hh, mm, ss)
        except Exception:
            continue
        if cand > base_dt:
            return cand
    return None

def _next_valid_day_of_month_after(base_dt: datetime, day: int, hh: int, mm: int, ss: int):
    y = base_dt.year
    m = base_dt.month
    for _ in range(0, 14):
        try:
            cand = datetime(y, m, day, hh, mm, ss)
            if cand > base_dt:
                return cand
        except Exception:
            pass

        m += 1
        if m > 12:
            m = 1
            y += 1
    return None

def _timer_parse_absolute_spec(text: str) -> tuple[Optional[int], str]:
    s = (text or "").strip()
    if not s:
        return None, _timer_invalid_abs_error()

    toks = s.split()
    if len(toks) > 2:
        return None, _timer_invalid_abs_error()

    now_dt = datetime.now()

    time_part = None
    date_part = None

    for tok in toks:
        pt = _parse_time_token(tok)
        pd = _parse_date_token(tok)

        if pt and not time_part:
            time_part = pt
            continue
        if pd and not date_part:
            date_part = pd
            continue
        return None, _timer_invalid_abs_error()

    if not time_part and not date_part:
        return None, _timer_invalid_abs_error()

    hh, mm, ss = time_part if time_part else (0, 0, 1)

    # Только время
    if time_part and not date_part:
        cand = now_dt.replace(hour=hh, minute=mm, second=ss, microsecond=0)
        if cand <= now_dt:
            cand = cand + timedelta(days=1)
        if int((cand - now_dt).total_seconds()) > TIMER_MAX_SECONDS:
            return None, "📑 Максимальный срок таймера — один год."
        return int(cand.timestamp()), ""

    day = int(date_part["day"] or 0)
    month = date_part["month"]
    year = date_part["year"]

    if day <= 0 or day > 31:
        return None, _timer_invalid_abs_error()

    cand = None

    # Полная дата
    if year is not None and month is not None:
        try:
            cand = datetime(int(year), int(month), int(day), hh, mm, ss)
        except Exception:
            return None, _timer_invalid_abs_error()

        if cand <= now_dt:
            return None, "📑 Нельзя установить таймер задним числом."

    # День + месяц
    elif month is not None:
        if month < 1 or month > 12:
            return None, _timer_invalid_abs_error()
        cand = _next_valid_month_day_after(now_dt, day, int(month), hh, mm, ss)
        if cand is None:
            return None, _timer_invalid_abs_error()

    # Только день
    else:
        cand = _next_valid_day_of_month_after(now_dt, day, hh, mm, ss)
        if cand is None:
            return None, _timer_invalid_abs_error()

    delta_sec = int((cand - now_dt).total_seconds())
    if delta_sec <= 0:
        return None, "📑 Нельзя установить таймер задним числом."
    if delta_sec > TIMER_MAX_SECONDS:
        return None, "📑 Максимальный срок таймера — один год."

    return int(cand.timestamp()), ""

def _timer_body_command(text: str) -> str:
    _first, body = _timer_first_line_and_body(text)
    return (body or "").strip()

def _timer_validate_body_command(cmd_text: str) -> tuple[bool, str]:
    raw = (cmd_text or "").strip()
    if not raw:
        return False, "📑 Неверный формат команды. Я вас не понимаю."

    parsed = parse_message_as_command(raw)
    if not parsed:
        return False, "📑 Команда для таймера не распознана."

    if parsed.cmd in (
        "timer_add_rel", "timer_add_abs", "timer_add_cycle",
        "timer_delete", "timer_clear_all", "timer_list",
        "owner", "owner_remove", "my_owner", "my_owner_remove",
        "agent", "agent_remove", "agents_panel",
        "bot_ban", "bot_unban", "remake_lab",
        "report", "settings", "blacklist", "users_list",
        "name_lock_lab", "name_lock_pat"
    ):
        return False, "📑 Эта команда не может быть выполнена таймером."

    return True, ""

def _timer_rows_for_user(user_id: int) -> List[sqlite3.Row]:
    return db_all(
        "SELECT timer_id, user_id, chat_id, created_at, next_run_ts, is_cycle, repeat_spec, cycle_total, cycle_left, command_text "
        "FROM user_timers WHERE user_id=? "
        "ORDER BY next_run_ts ASC, timer_id ASC",
        (int(user_id),)
    ) or []

def _timer_create(
    user_id: int,
    chat_id: int,
    next_run_ts: int,
    is_cycle: int,
    repeat_spec: dict,
    command_text: str,
    cycle_total: int = 0,
    cycle_left: int = 0
):
    db_exec(
        "INSERT INTO user_timers(user_id, chat_id, created_at, next_run_ts, is_cycle, repeat_spec, cycle_total, cycle_left, command_text) "
        "VALUES (?,?,?,?,?,?,?,?,?)",
        (
            int(user_id),
            int(chat_id),
            int(now_ts()),
            int(next_run_ts),
            int(is_cycle),
            json.dumps(repeat_spec or {}, ensure_ascii=False),
            int(cycle_total or 0),
            int(cycle_left or 0),
            str(command_text or "").strip(),
        ),
        commit=True
    )

def _timer_row_to_display(index_num: int, row: sqlite3.Row) -> str:
    next_ts = int(row["next_run_ts"] or 0)
    is_cycle = int(row["is_cycle"] or 0)
    cycle_left = int(row["cycle_left"] or 0)
    cycle_total = int(row["cycle_total"] or 0)

    cmd = (row["command_text"] or "").strip()
    first_cmd = cmd.splitlines()[0].strip() if cmd else "—"
    if len(first_cmd) > 42:
        first_cmd = first_cmd[:42] + "…"

    mark = premium_emoji_html("🔁") if is_cycle == 1 else premium_emoji_html("⏰")

    suffix = ""
    if is_cycle == 1:
        try:
            spec = json.loads((row["repeat_spec"] or "") or "{}")
            suffix = f" | {_timer_spec_to_text(spec)}"
        except Exception:
            suffix = ""

        if cycle_total > 0:
            suffix += f" | осталось: {cycle_left}/{cycle_total}"

    return f"{index_num}. {mark} {_fmt_ts(next_ts)}{suffix}\n<code>{h(first_cmd)}</code>"

def render_timer_list_text(user_id: int) -> str:
    uid = int(user_id)

    u = get_user_row(uid)
    scope_name = (
        display_name(
            u["first_name"] or "",
            u["last_name"] or "",
            u["username"] or "",
            int(uid)
        ) if u else str(uid)
    )

    rows = _timer_rows_for_user(uid)

    lines = []
    lines.append(f"{premium_emoji_html('⏳')} Список таймеров {h(scope_name)}")
    lines.append("")

    if not rows:
        lines.append("<blockquote>Список пока пуст.</blockquote>")
    else:
        lines.append("<blockquote expandable>")
        for i, row in enumerate(rows, 1):
            lines.append(_timer_row_to_display(i, row))
            if i < len(rows):
                lines.append("")
        lines.append("</blockquote>")

    lines.append("")
    lines.append("💬 Вы можете создать таймер командами:\n\"<code>таймер через</code> {период}\"\n\"<code>таймер на</code> {период}\"\n\"<code>таймер цикл</code> {число срабатываний} {период}\"\nи далее ввести текст команды на исполнения")
    return "\n".join(lines)

def _make_fake_timer_message(user_id: int, chat_id: int, text: str):
    class _FakeUser:
        pass

    class _FakeChat:
        pass

    class _FakeMsg:
        pass

    u = get_user_row(int(user_id))

    placeholder = None
    try:
        placeholder = _REAL_BOT_SEND_MESSAGE(int(chat_id), "⏳")
    except Exception as e:
        if _is_chat_not_found_error(e):
            return None, None
        raise

    fu = _FakeUser()
    fu.id = int(user_id)
    fu.username = (u["username"] or "") if u else ""
    fu.first_name = (u["first_name"] or "") if u else ""
    fu.last_name = (u["last_name"] or "") if u else ""
    fu.is_bot = False

    fc = _FakeChat()
    fc.id = int(chat_id)
    fc.type = "private" if int(chat_id) == int(user_id) else "group"

    fm = _FakeMsg()
    fm.from_user = fu
    fm.chat = fc
    fm.text = str(text or "")
    fm.message_id = int(placeholder.message_id) if placeholder is not None else 0
    fm.reply_to_message = None
    fm.via_bot = None
    fm.content_type = "text"
    fm.date = now_ts()

    return fm, placeholder

def _execute_timer_command_text(user_id: int, chat_id: int, command_text: str):
    cmd_text = (command_text or "").strip()
    if not cmd_text:
        return

    parsed = parse_message_as_command(cmd_text)
    if not parsed:
        try:
            _REAL_BOT_SEND_MESSAGE(int(chat_id), "📑 Таймер сработал, но текст команды не распознан.")
        except Exception as e:
            if _is_chat_not_found_error(e):
                raise RuntimeError("__TIMER_DEAD_CHAT__")
            raise
        return

    if parsed.cmd in (
        "timer_add_rel", "timer_add_abs", "timer_add_cycle",
        "timer_delete", "timer_clear_all", "timer_list",
        "owner", "owner_remove", "my_owner", "my_owner_remove",
        "agent", "agent_remove", "agents_panel",
        "bot_ban", "bot_unban", "remake_lab",
        "report", "settings", "blacklist",
        "name_lock_lab", "name_lock_pat"
    ):
        try:
            _REAL_BOT_SEND_MESSAGE(int(chat_id), "📑 Эта команда не может быть выполнена таймером.")
        except Exception as e:
            if _is_chat_not_found_error(e):
                raise RuntimeError("__TIMER_DEAD_CHAT__")
            raise
        return

    fake_msg = None
    placeholder = None
    try:
        fake_msg, placeholder = _make_fake_timer_message(int(user_id), int(chat_id), cmd_text)
        if fake_msg is None:
            raise RuntimeError("__TIMER_DEAD_CHAT__")
        text_router(fake_msg)
    finally:
        if placeholder is not None:
            try:
                bot.delete_message(int(placeholder.chat.id), int(placeholder.message_id))
            except Exception:
                pass

def _timer_reschedule_from_row(row: sqlite3.Row, now_ts_value: int) -> tuple[Optional[int], Optional[int]]:
    if int(row["is_cycle"] or 0) != 1:
        return None, None

    try:
        spec = json.loads((row["repeat_spec"] or "") or "{}")
    except Exception:
        return None, None

    cycle_left = int(row["cycle_left"] or 0)
    if cycle_left <= 1:
        return None, None

    base_dt = datetime.fromtimestamp(int(row["next_run_ts"] or 0))
    nxt = _timer_apply_period(base_dt, spec)

    guard = 0
    while int(nxt.timestamp()) <= int(now_ts_value) and guard < 500:
        nxt = _timer_apply_period(nxt, spec)
        guard += 1

    if guard >= 500:
        return None, None

    return int(nxt.timestamp()), int(cycle_left - 1)

def _run_due_timers(now_value: int):
    rows = db_all(
        "SELECT timer_id, user_id, chat_id, created_at, next_run_ts, is_cycle, repeat_spec, cycle_total, cycle_left, command_text "
        "FROM user_timers WHERE next_run_ts>0 AND next_run_ts<=? "
        "ORDER BY next_run_ts ASC, timer_id ASC LIMIT 50",
        (int(now_value),)
    ) or []

    for row in rows:
        timer_id = int(row["timer_id"])
        user_id = int(row["user_id"])
        chat_id = int(row["chat_id"] or user_id)

        transient_failed = False

        try:
            _execute_timer_command_text(user_id, chat_id, row["command_text"] or "")
        except Exception as e:
            if "__TIMER_DEAD_CHAT__" in str(e):
                db_exec("DELETE FROM user_timers WHERE timer_id=?", (timer_id,), commit=True)
                continue
            if _is_transient_telegram_network_error(e):
                transient_failed = True
            else:
                send_error_report(f"_run_due_timers#{timer_id}", e)

        if transient_failed:
            continue

        next_cycle_ts, new_left = _timer_reschedule_from_row(row, now_value)
        if next_cycle_ts is None:
            db_exec("DELETE FROM user_timers WHERE timer_id=?", (timer_id,), commit=True)
        else:
            db_exec(
                "UPDATE user_timers SET next_run_ts=?, cycle_left=? WHERE timer_id=?",
                (int(next_cycle_ts), int(new_left), int(timer_id)),
                commit=True
            )

# форматы слов
def _fmt_num(n: int) -> str:
    return f"{int(n):,}".replace(",", " ")

def _fmt_bio_res(n: int) -> str:
    w = _ru_form(n, "био-ресурс", "био-ресурса", "био-ресурсов")
    return f"🧬 {_fmt_num(n)} {w}"

def _fmt_bio_mater(n: int) -> str:
    w = _ru_form(n, "био-материал", "био-материала", "био-материалов")
    return f"💊 {_fmt_num(n)} {w}"

# форматы чисел
def _split_3_groups(n: int) -> list[str]:
    s = str(abs(int(n)))
    if not s:
        return ["0"]
    groups = []
    while s:
        groups.append(s[-3:])
        s = s[:-3]
    return groups[::-1]

def _fmt_groups_dots(groups: list[str]) -> str:
    if not groups:
        return "0"
    out = [groups[0]]
    for g in groups[1:]:
        out.append(g.zfill(3))
    return ".".join(out)

def _fmt_k(n: int) -> str:
    """
    143657584 -> 143.657k
    1234986   -> 1.234k
    12345678912 -> 12.345kk
    """
    n = int(n)
    sign = "-" if n < 0 else ""
    groups = _split_3_groups(n)
    if len(groups) <= 2:
        return sign + _fmt_groups_dots(groups)
    head = [groups[0], groups[1].zfill(3)]
    return sign + ".".join(head) + ("k" * (len(groups) - 2))

def _rget(row, key: str, default=None):
    """Безопасно читает значение из sqlite3.Row/dict."""
    try:
        if row is None:
            return default
        if isinstance(row, dict):
            return row.get(key, default)
        # sqlite3.Row
        if hasattr(row, "keys") and key in row.keys():
            return row[key]
        return default
    except Exception:
        return default

# шанс коэффицента
def _pick_cof_rost() -> int:
    r = random.random() * 100.0

    if r < 42.10:
        return 1
    if r < 42.10 + 23.54:
        return 2
    if r < 42.10 + 23.54 + 18.45:
        return 3
    if r < 42.10 + 23.54 + 18.45 + 9.02:
        return 4
    if r < 42.10 + 23.54 + 18.45 + 9.02 + 2.99:
        return 5
    if r < 42.10 + 23.54 + 18.45 + 9.02 + 2.99 + 1.84:
        return 6
    if r < 42.10 + 23.54 + 18.45 + 9.02 + 2.99 + 1.84 + 1.03:
        return 7
    if r < 42.10 + 23.54 + 18.45 + 9.02 + 2.99 + 1.84 + 1.03 + 0.71:
        return 8
    if r < 42.10 + 23.54 + 18.45 + 9.02 + 2.99 + 1.84 + 1.03 + 0.71 + 0.23:
        return 9
    return 10

# стартовые значения
SYNTH_COOLDOWN_SEC = 4 * 3600 # синтезация кулдаун
FEVER_SEC = 60                 # горячка 1 мин
INF_DAY = 1                    # заражение период 1 день

VACCINE_PRICE_BASE = 50
VACCINE_PRICE_STEP = 50
VACCINE_PRICE_EVERY_AVG_LVLS = 20
VACCINE_PRICE_MAX = 2500

FEVER_MAX_SEC = 3 * 3600  # максимум горячки 3 часа
REINFECT_CD_SEC = 6 * 3600     # перезаражение 6 часов

# Константы
CB_BUY_VACCINE = "vac:buy"
CB_USE_VACCINE = "vac:use"
CB_USE_VACCINE_X = "vac:usex"
CB_LAB_DELETE_OK = "labdel:ok"
CB_LAB_DELETE_CANCEL = "labdel:cancel"
CB_LAB_CREATE = "lab:create"
CB_LAB_RESTORE = "lab:restore"
CB_LAB_RESTORE_REQ = "lab:restore:req"
LAB_DELETE_PHRASE = "Да, я полностью уверен"
CB_AO_MENU = "ao:menu"
CB_AO_TOGGLE = "ao:toggle"
CB_CORP_JOIN = "corp:join"
CB_CORP_REQ_APPROVE = "corp:req:ok"
CB_CORP_REQ_REJECT = "corp:req:no"
CB_CORP_INV_ACCEPT = "corp:inv:ok"
CB_CORP_INV_REJECT = "corp:inv:no"
CB_CORP_TX = "corpmix"
CB_RP_ACCEPT = "rp:ok"
CB_RP_DECLINE = "rp:no"
#            callback_data
LABUI_TAG = "L"   
BALUI_TAG = "C"
INFUI_TAG = "Z"
UPGUI_TAG = "U"
CORPUI_TAG = "G"
TOPUI_TAG = "T"
SETUI_TAG = "W"
REPORTUI_TAG = "Y"
BLUI_TAG = "K"
USERSUI_TAG = "US"
CHATSUI_TAG = "UC"
EMPACKUI_TAG = "EP"
PROMOUI_TAG = "PR"
DBSTATUI_TAG = "DBS"
DBFILEUI_TAG = "DBF"
PROMO_PAGE_SIZE = 15
#           balance-chain kinds
BALCHAIN_UPGRADE = "upgrade"
BALCHAIN_CORP_TRANSFER = "corp_transfer"
BALCHAIN_VACCINE = "vaccine"
BALCHAIN_DUEL_STAKE = "duel_stake"
BALCHAIN_DUEL_BET = "duel_bet"

# хендлеры и хэлперы
#           report
REPORT_CATS = {
    "BUG": "Ошибка бота",
    "USER": "Жалоба на пользователя",
    "APPEAL": "Апелляция",
    "RESTORE": "Восстановление лаборатории",
    "OTHER": "Другое",
}
#           Заражение
INF_MODE_SYNONYMS = {
    "р": "r", "рандом": "r",
    "+": "p", "б": "p", "больше": "p",
    "-": "m", "м": "m", "меньше": "m",
    "=": "e", "равный": "e",
    "чат": "c",
}

INF_CHAT_FILTER_SYNONYMS = {
    "+": "p", "б": "p", "больше": "p",
    "-": "m", "м": "m", "меньше": "m",
    "=": "e", "равный": "e",
}

#           промокод
_PROMO_THEME_A = [
    "BIO", "LAB", "PATHOGEN", "CORP", "GENOME", "SYNTH", "CELL", "VECTOR",
    "OUTBREAK", "QUARANTINE", "VIRUS", "MED", "IMMUNE", "PLAGUE", "TOXIN"
]
_PROMO_THEME_B = [
    "CORE", "NOVA", "DELTA", "OMEGA", "NEXUS", "SECTOR", "REACTOR",
    "PROTO", "ALPHA", "BETA", "GAMMA", "SIGMA", "XENO", "ECHO", "RIFT"
]

def _promo_norm_code(code: str) -> str:
    return re.sub(r"\s+", " ", (code or "").strip()).casefold()

def _promo_make_random_code() -> str:
    left = random.choice(_PROMO_THEME_A)
    right = random.choice(_PROMO_THEME_B)
    num = random.randint(10, 9999)

    pattern = random.randint(1, 7)
    if pattern == 1:
        return f"{left}-{right}{num}"
    if pattern == 2:
        return f"{left}_{right}_{num}"
    if pattern == 3:
        return f"{left}{num}{right}{num}"
    if pattern == 4:
        return f"{left}{num}-{right}"
    if pattern == 5:
        return f"{num}_{left}{right}"
    if pattern == 6:
        return f"{num}{left}¦{num}{right}"
    return f"{left}{right}{num}"

def _promo_bonus_skill_code_from_prefix(line: str) -> tuple[Optional[str], int]:
    toks = (line or "").strip().split()
    if len(toks) < 2:
        return None, 0

    for take in range(min(3, len(toks) - 1), 0, -1):
        probe = " ".join(toks[:take])
        code = _resolve_skill(probe)
        if code and toks[take].isdigit():
            return code, int(toks[take])

    return None, 0

def _promo_parse_bonus_line(line: str):
    s = re.sub(r"\s+", " ", (line or "").strip())
    if not s:
        return None

    low = s.lower()
    toks = s.split()

    code, amt = _promo_bonus_skill_code_from_prefix(s)
    if code and amt > 0:
        return {"kind": "skill", "ref_code": code, "amount": amt}

    if low.startswith("очков навыка ") or low.startswith("очков "):
        last = toks[-1]
        if last.isdigit():
            return {"kind": "points", "ref_code": "", "amount": int(last)}

    if low.startswith("очко навыка "):
        last = toks[-1]
        if last.isdigit():
            return {"kind": "points", "ref_code": "", "amount": int(last)}

    if low.startswith("био-ресурсы ") or low.startswith("ресы ") or low.startswith("био-ресурс "):
        last = toks[-1]
        if last.isdigit():
            return {"kind": "res", "ref_code": "", "amount": int(last)}

    if low.startswith("био-материалы ") or low.startswith("маты ") or low.startswith("био-материал "):
        last = toks[-1]
        if last.isdigit():
            return {"kind": "mat", "ref_code": "", "amount": int(last)}

    return None

def _promo_parse_create_message(message_text: str):
    raw = strip_bio_prefix((message_text or "").strip())
    if not raw:
        return None, "📑 Неверный формат команды."

    first_line, body = _timer_first_line_and_body(raw)
    fl = first_line.strip()
    if fl.startswith("/") or fl.startswith("."):
        fl = fl[1:].strip()

    parts = fl.split(None, 1)
    if len(parts) < 2:
        return None, "📑 Неверный формат команды."

    header = parts[1].strip()
    low = header.lower()

    is_permanent = 0
    expires_ts = 0
    code = ""

    if low.startswith("постоянный "):
        is_permanent = 1
        code = header[len("постоянный "):].strip()
    elif low.startswith("временный "):
        tail = header[len("временный "):].strip()
        toks = tail.split()
        parsed = False
        for take in (2, 1):
            if len(toks) >= take:
                ts, err = _timer_parse_absolute_spec(" ".join(toks[:take]))
                if ts is not None:
                    expires_ts = int(ts)
                    code = " ".join(toks[take:]).strip()
                    parsed = True
                    break
        if not parsed:
            return None, f"📑 Неверный формат периода промокода.\n{_TIMER_ABS_FORMATS_HELP}"
    else:
        return None, "📑 Укажите параметр <code>постоянный</code> или <code>временный</code>."

    if not code:
        return None, "📑 Укажите название промокода."

    bonus_lines = [x.strip() for x in body.splitlines() if x.strip()]
    if not bonus_lines:
        return None, (
            "📑 Укажите бонусы с новой строки.\n"
            "Поддерживаемые форматы:\n"
            "<blockquote expandable>\n"
            "заразность n\n"
            "синтез n\n"
            "ускорение n\n"
            "очков навыка n\n"
            "био-ресурсы n\n"
            "био-материалы n\n"
            "</blockquote>"
        )

    bonuses = []
    for line in bonus_lines:
        b = _promo_parse_bonus_line(line)
        if not b or int(b["amount"]) <= 0:
            return None, (
                "📑 Неверный формат бонусов.\n"
                "Поддерживаемые форматы:\n"
                "<blockquote expandable>\n"
                "заразность n\n"
                "синтез n\n"
                "ускорение n\n"
                "очков навыка n\n"
                "био-ресурсы n\n"
                "био-материалы n\n"
                "</blockquote>"
            )
        bonuses.append(b)

    return {
        "is_permanent": int(is_permanent),
        "expires_ts": int(expires_ts),
        "code": code,
        "code_key": _promo_norm_code(code),
        "bonuses": bonuses,
    }, ""

def _promo_bonus_to_text(b) -> str:
    if b is None:
        return ""

    if isinstance(b, dict):
        kind = str(b.get("kind") or "")
        amount = int(b.get("amount") or 0)
        ref_code = str(b.get("ref_code") or "")
    else:
        kind = str(b["kind"] or "")
        amount = int(b["amount"] or 0)
        ref_code = str(b["ref_code"] or "")

    if kind == "skill":
        skill = SKILLS.get(ref_code)
        if skill:
            return f"{skill['emoji']} +{amount}"
        return f"🔹 {h(ref_code)} +{amount}"

    if kind == "points":
        pts_word = _ru_form(amount, "очко навыка", "очка навыка", "очков навыка")
        return f"🔹 +{amount} {pts_word}"

    if kind == "res":
        return f"🧬 +{amount}"

    if kind == "mat":
        return f"💊 +{amount}"

    return ""

def _promo_fetch_all_rows():
    return db_all(
        "SELECT promo_id, code, code_key, is_permanent, expires_ts, created_at "
        "FROM promo_codes ORDER BY created_at DESC, promo_id DESC"
    ) or []

def _promo_cb(page: int) -> str:
    return f"{PROMOUI_TAG}:{int(page)}"

def _promo_parse_cb(data: str) -> Optional[int]:
    try:
        p = (data or "").split(":")
        if len(p) != 2 or p[0] != PROMOUI_TAG:
            return None
        return int(p[1])
    except Exception:
        return None

def render_promocode_list_text(page: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    rows = _promo_fetch_all_rows()
    total = len(rows)
    if total <= 0:
        return "📋 Список промокодов:\n<blockquote>Список пуст.</blockquote>", None

    total_pages = max(1, (total + PROMO_PAGE_SIZE - 1) // PROMO_PAGE_SIZE)
    page = max(1, min(int(page), total_pages))
    start = (page - 1) * PROMO_PAGE_SIZE
    part = rows[start:start + PROMO_PAGE_SIZE]

    lines = ["📋 Список промокодов:"]
    lines.append("<blockquote expandable>")
    for idx, r in enumerate(part, start + 1):
        promo_id = int(r["promo_id"])
        if int(r["is_permanent"] or 0) == 1:
            status_txt = "постоянный"
        else:
            status_txt = f"действителен до {_fmt_ts(int(r['expires_ts'] or 0))}"

        bonuses = db_all(
            "SELECT kind, ref_code, amount FROM promo_bonuses WHERE promo_id=? ORDER BY bonus_id ASC",
            (promo_id,)
        ) or []
        bonus_parts = []
        for b in bonuses:
            bt = _promo_bonus_to_text(b)
            if bt:
                bonus_parts.append(bt)
        bonus_txt = " ".join(bonus_parts).strip()
        lines.append(f"{idx}| <code>{h(r['code'])}</code> - {status_txt}")
        if bonus_txt:
            lines.append(bonus_txt)

    lines.append("</blockquote>")

    kb = None
    if total_pages > 1:
        kb = InlineKeyboardMarkup(row_width=8)
        row_btns = []
        if page > 2:
            row_btns.append(InlineKeyboardButton("<<", callback_data=_promo_cb(1)))
        if page > 1:
            row_btns.append(InlineKeyboardButton("<", callback_data=_promo_cb(page - 1)))

        page_nums = []
        if total_pages <= 4:
            page_nums = list(range(1, total_pages + 1))
        elif page == 1:
            page_nums = [1, 2, 3, 4]
        elif page == total_pages:
            page_nums = [total_pages - 3, total_pages - 2, total_pages - 1, total_pages]
        else:
            page_nums = [max(1, page - 1), page, min(total_pages, page + 1), min(total_pages, page + 2)]
            page_nums = sorted(dict.fromkeys([p for p in page_nums if 1 <= p <= total_pages]))

        for p in page_nums:
            if p == page:
                row_btns.append(InlineKeyboardButton(f"·{p}·", callback_data=_promo_cb(page)))
            else:
                row_btns.append(InlineKeyboardButton(str(p), callback_data=_promo_cb(p)))

        if page < total_pages:
            row_btns.append(InlineKeyboardButton(">", callback_data=_promo_cb(page + 1)))
        if page < total_pages - 1:
            row_btns.append(InlineKeyboardButton(">>", callback_data=_promo_cb(total_pages)))

        kb.row(*row_btns)

    return "\n".join(lines), kb

def _promo_create(code: str, is_permanent: int, expires_ts: int, bonuses: list, creator_id: int):
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT INTO promo_codes(code, code_key, is_permanent, expires_ts, created_at, created_by) VALUES (?,?,?,?,?,?)",
                (code, _promo_norm_code(code), int(is_permanent), int(expires_ts), int(now_ts()), int(creator_id))
            )
            promo_id = int(c.lastrowid)
            for b in bonuses:
                c.execute(
                    "INSERT INTO promo_bonuses(promo_id, kind, ref_code, amount) VALUES (?,?,?,?)",
                    (promo_id, str(b["kind"]), str(b.get("ref_code") or ""), int(b["amount"]))
                )
            conn.commit()
            return promo_id
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _promo_apply_to_user(code: str, user_id: int) -> tuple[bool, str]:
    ensure_lab_exists(int(user_id))
    row = db_one(
        "SELECT promo_id, code, is_permanent, expires_ts FROM promo_codes WHERE code_key=? LIMIT 1",
        (_promo_norm_code(code),)
    )
    if not row:
        return False, "📑 Промокод не найден."

    promo_id = int(row["promo_id"])
    if int(row["is_permanent"] or 0) != 1:
        exp = int(row["expires_ts"] or 0)
        if exp > 0 and exp < now_ts():
            return False, "📑 Срок действия промокода истёк."

    used = db_one("SELECT 1 FROM promo_uses WHERE promo_id=? AND user_id=? LIMIT 1", (promo_id, int(user_id)))
    if used:
        return False, "📑 Вы уже использовали этот промокод."

    bonuses = db_all(
        "SELECT kind, ref_code, amount FROM promo_bonuses WHERE promo_id=? ORDER BY bonus_id ASC",
        (promo_id,)
    ) or []
    if not bonuses:
        return False, "📑 Это промокод пустышка."

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            for b in bonuses:
                kind = str(b["kind"] or "")
                ref = str(b["ref_code"] or "")
                amt = int(b["amount"] or 0)
                if amt <= 0:
                    continue

                if kind == "skill" and ref in SKILLS:
                    col = SKILLS[ref]["col"]
                    c.execute(f"UPDATE labs SET {col}=COALESCE({col},1)+? WHERE user_id=?", (amt, int(user_id)))
                elif kind == "points":
                    c.execute("UPDATE labs SET skill_points=COALESCE(skill_points,0)+? WHERE user_id=?", (amt, int(user_id)))
                elif kind == "res":
                    c.execute(
                        "UPDATE labs SET all_bio_res=COALESCE(all_bio_res,0)+?, bio_res=COALESCE(bio_res,0)+? WHERE user_id=?",
                        (amt, amt, int(user_id))
                    )
                elif kind == "mat":
                    c.execute("UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? WHERE user_id=?", (amt, int(user_id)))

            c.execute(
                "INSERT INTO promo_uses(promo_id, user_id, used_at) VALUES (?,?,?)",
                (promo_id, int(user_id), int(now_ts()))
            )
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    _recalc_derived(int(user_id))
    pretty_parts = []
    for b in bonuses:
        bt = _promo_bonus_to_text(b)
        if bt:
            pretty_parts.append(bt)
    pretty = " ".join(pretty_parts).strip()
    return True, f"🎁 Промокод <code>{h(row['code'])}</code> активирован.\n{pretty}"

# расчёт коэффициентов
INFECT_BOUND_K = 30 # коэффициент масштаба
INFECT_BOUND_BETA = 0.7 # коэффициент кривизны
COFINFUI_TAG = "CI"
COFDUELUI_TAG = "CD"

def load_infect_formula_settings():
    global INFECT_BOUND_K, INFECT_BOUND_BETA

    row = db_one(
        "SELECT COALESCE(k_value,30.0) AS k_value, COALESCE(beta_value,0.7) AS beta_value "
        "FROM infect_formula_settings WHERE settings_id=1 LIMIT 1"
    )
    if not row:
        return

    try:
        INFECT_BOUND_K = float(row["k_value"])
    except Exception:
        INFECT_BOUND_K = 30.0

    try:
        INFECT_BOUND_BETA = float(row["beta_value"])
    except Exception:
        INFECT_BOUND_BETA = 0.7

def save_infect_formula_settings(k_value: float, beta_value: float):
    global INFECT_BOUND_K, INFECT_BOUND_BETA

    INFECT_BOUND_K = float(k_value)
    INFECT_BOUND_BETA = float(beta_value)

    db_exec(
        "INSERT INTO infect_formula_settings(settings_id, k_value, beta_value, updated_at) "
        "VALUES (1,?,?,?) "
        "ON CONFLICT(settings_id) DO UPDATE SET "
        "k_value=excluded.k_value, beta_value=excluded.beta_value, updated_at=excluded.updated_at",
        (float(INFECT_BOUND_K), float(INFECT_BOUND_BETA), int(now_ts())),
        commit=True
    )

def _parse_edit_float_arg(s: str):
    raw = (s or "").strip().replace(",", ".")
    if not raw:
        return None
    try:
        return float(raw)
    except Exception:
        return None

def _parse_edit_int_arg(s: str):
    raw = (s or "").strip().replace(",", ".")
    if not raw:
        return None
    try:
        if "." in raw:
            return None
        return int(raw)
    except Exception:
        return None

def _cof_inf_stats_cb() -> str:
    return f"{COFINFUI_TAG}:R"

def kb_cof_inf_stats() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Обновить статистику", callback_data=_cof_inf_stats_cb()))
    return kb

HINT_ON_COEFFICIENTS = (
    "<b>k — коэффициент масштаба</b>\n"
    "Управляет тем, на каких уровнях начнётся заметное расширение диапазона и усиление разницы.\n"
    "▸ больше k — всё меняется медленнее\n"
    "▸ меньше k — всё меняется быстрее\n\n"
    "<b>β — коэффициент кривизны</b>\n"
    "Управляет формой роста.\n"
    "▸ β&lt;1 — изменения начинаются раньше и плавнее\n"
    "▸ β=1 — умеренный вариант\n"
    "▸ β&gt;1 — долго плавно, потом резче"
)

def render_cof_inf_stats_text() -> str:
    pairs = [(1, 2), (10, 20), (19, 20), (1, 100), (1, 1000)]

    lines = []
    lines.append("📋 Изменения формулы заражения")
    lines.append(f"<blockquote expandable>{HINT_ON_COEFFICIENTS}</blockquote>")
    lines.append("")
    lines.append(f"Коэф. масштаба (k): {str(INFECT_BOUND_K).replace('.', ',')}")
    lines.append(f"Коэф. искривления (β): {str(INFECT_BOUND_BETA).replace('.', ',')}")
    lines.append("")
    lines.append("Z | I | P(усп) | P(пров)")

    for z, i in pairs:
        p_success = float(infect_success_chance(z, i))
        p_fail = 100.0 - p_success
        lines.append(f"{z} | {i} | {_fmt_pct_text(p_success)} | {_fmt_pct_text(p_fail)}")

    return "\n".join(lines)

# формула дуэли
def load_duel_formula_settings():
    global DUEL_MAX_TURNS, DUEL_BASE_HIT_PCT, DUEL_AIM_STEP_PCT, DUEL_BREAK_BASE_PCT, DUEL_BREAK_STEP_PCT

    row = db_one(
        "SELECT "
        "COALESCE(rounds_value,40) AS rounds_value, "
        "COALESCE(base_hit_pct,20) AS base_hit_pct, "
        "COALESCE(aim_step_pct,8) AS aim_step_pct, "
        "COALESCE(break_base_pct,22) AS break_base_pct, "
        "COALESCE(break_step_pct,8) AS break_step_pct "
        "FROM duel_formula_settings WHERE settings_id=1 LIMIT 1"
    )
    if not row:
        return

    try:
        DUEL_MAX_TURNS = int(row["rounds_value"])
    except Exception:
        DUEL_MAX_TURNS = 40

    try:
        DUEL_BASE_HIT_PCT = int(row["base_hit_pct"])
    except Exception:
        DUEL_BASE_HIT_PCT = 20

    try:
        DUEL_AIM_STEP_PCT = int(row["aim_step_pct"])
    except Exception:
        DUEL_AIM_STEP_PCT = 8

    try:
        DUEL_BREAK_BASE_PCT = int(row["break_base_pct"])
    except Exception:
        DUEL_BREAK_BASE_PCT = 22

    try:
        DUEL_BREAK_STEP_PCT = int(row["break_step_pct"])
    except Exception:
        DUEL_BREAK_STEP_PCT = 8

def save_duel_formula_settings(
    rounds_value: int | None = None,
    base_hit_pct: int | None = None,
    aim_step_pct: int | None = None,
    break_base_pct: int | None = None,
    break_step_pct: int | None = None
):
    global DUEL_MAX_TURNS, DUEL_BASE_HIT_PCT, DUEL_AIM_STEP_PCT, DUEL_BREAK_BASE_PCT, DUEL_BREAK_STEP_PCT

    if rounds_value is not None:
        DUEL_MAX_TURNS = int(rounds_value)
    if base_hit_pct is not None:
        DUEL_BASE_HIT_PCT = int(base_hit_pct)
    if aim_step_pct is not None:
        DUEL_AIM_STEP_PCT = int(aim_step_pct)
    if break_base_pct is not None:
        DUEL_BREAK_BASE_PCT = int(break_base_pct)
    if break_step_pct is not None:
        DUEL_BREAK_STEP_PCT = int(break_step_pct)

    db_exec(
        "INSERT INTO duel_formula_settings("
        "settings_id, rounds_value, base_hit_pct, aim_step_pct, break_base_pct, break_step_pct, updated_at"
        ") VALUES (1,?,?,?,?,?,?) "
        "ON CONFLICT(settings_id) DO UPDATE SET "
        "rounds_value=excluded.rounds_value, "
        "base_hit_pct=excluded.base_hit_pct, "
        "aim_step_pct=excluded.aim_step_pct, "
        "break_base_pct=excluded.break_base_pct, "
        "break_step_pct=excluded.break_step_pct, "
        "updated_at=excluded.updated_at",
        (
            int(DUEL_MAX_TURNS),
            int(DUEL_BASE_HIT_PCT),
            int(DUEL_AIM_STEP_PCT),
            int(DUEL_BREAK_BASE_PCT),
            int(DUEL_BREAK_STEP_PCT),
            int(now_ts())
        ),
        commit=True
    )

def _cof_duel_stats_cb() -> str:
    return f"{COFDUELUI_TAG}:R"

def kb_duel_cof_stats() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Обновить статистику", callback_data=_cof_duel_stats_cb()))
    return kb

def render_duel_cof_stats_text() -> str:
    stack1_aim = int(DUEL_AIM_STEP_PCT)
    stack3_aim = int(DUEL_AIM_STEP_PCT * 3)

    stack1_break = int(_duel_break_chance_from_bonus(stack1_aim)) if stack1_aim > 0 else int(DUEL_BREAK_BASE_PCT)
    stack3_break = int(_duel_break_chance_from_bonus(stack3_aim)) if stack3_aim > 0 else int(DUEL_BREAK_BASE_PCT)

    lines = []
    lines.append("📋 Изменения формулы дуэли")
    lines.append("")
    lines.append(f"Ходов: {int(DUEL_MAX_TURNS)}")
    lines.append(f"Попадание: {_fmt_pct_text(float(DUEL_BASE_HIT_PCT))}")
    lines.append(f"Прицел бонус: +{_fmt_pct_text(float(DUEL_AIM_STEP_PCT))}")
    lines.append(f"Сбивание: {_fmt_pct_text(float(DUEL_BREAK_BASE_PCT))}")
    lines.append(f"Сбив. бонус: +{_fmt_pct_text(float(DUEL_BREAK_STEP_PCT))}")
    lines.append("")
    lines.append("Стак |+👁️‍🗨️|🪃")
    lines.append(f"ㅤㅤ1|{_fmt_pct_text(float(stack1_aim))}|{_fmt_pct_text(float(stack1_break))}")
    lines.append(f"ㅤㅤ3|{_fmt_pct_text(float(stack3_aim))}|{_fmt_pct_text(float(stack3_break))}")

    return "\n".join(lines)

# шансы заражения
def infect_success_chance(att_infect: int, tgt_imm: int) -> float:
    z = max(1.0, float(int(att_infect or 0)))
    i = max(1.0, float(int(tgt_imm or 0)))

    M = max(z, i)
    k = float(INFECT_BOUND_K)
    beta = float(INFECT_BOUND_BETA)

    if k <= 0.0:
        k = 0.000001
    if beta <= 0.0:
        beta = 0.000001

    mk = M / k
    mk_beta = mk ** beta

    # P_min(M) = 0.001 + 9.999 * e^(- (M / k)^beta)
    p_min = 0.001 + 9.999 * math.exp(-mk_beta)

    # P_max(M) = 100 - P_min(M)
    p_max = 100.0 - p_min

    # R = (Z - I) / min(Z, I)
    denom = min(z, i)
    if denom <= 0.0:
        denom = 1.0
    R = (z - i) / denom

    # S = tanh( R * (M / k)^beta )
    S = math.tanh(R * mk_beta)

    # P_усп = 50 + (50 - P_min(M)) * S
    p = 50.0 + (50.0 - p_min) * S

    if p < p_min:
        p = p_min
    elif p > p_max:
        p = p_max

    if p < 0.001:
        p = 0.001
    elif p > 99.999:
        p = 99.999

    return float(p)

FAIL_STACK_RESET_SEC = 30 * 60  # 30 минут

def _clear_infection_fail_stack(attacker_id: int, target_id: int):
    db_exec(
        "DELETE FROM infection_fail_stacks WHERE attacker_id=? AND target_id=?",
        (int(attacker_id), int(target_id)),
        commit=True
    )

def _get_infection_fail_stack(attacker_id: int, target_id: int, now_value: int | None = None) -> int:
    now_value = int(now_value if now_value is not None else now_ts())

    row = db_one(
        "SELECT COALESCE(fail_count,0) AS fc, COALESCE(last_fail_ts,0) AS lts "
        "FROM infection_fail_stacks WHERE attacker_id=? AND target_id=? LIMIT 1",
        (int(attacker_id), int(target_id))
    )
    if not row:
        return 0

    fail_count = int(row["fc"] or 0)
    last_fail_ts = int(row["lts"] or 0)

    if fail_count <= 0:
        return 0

    if last_fail_ts <= 0 or (now_value - last_fail_ts) > FAIL_STACK_RESET_SEC:
        _clear_infection_fail_stack(int(attacker_id), int(target_id))
        return 0

    return int(fail_count)

def _add_infection_fail_stack(attacker_id: int, target_id: int, now_value: int | None = None) -> int:
    now_value = int(now_value if now_value is not None else now_ts())
    current = _get_infection_fail_stack(int(attacker_id), int(target_id), now_value)
    new_count = int(current + 1)

    db_exec(
        "INSERT INTO infection_fail_stacks(attacker_id, target_id, fail_count, last_fail_ts) "
        "VALUES (?,?,?,?) "
        "ON CONFLICT(attacker_id, target_id) DO UPDATE SET "
        "fail_count=excluded.fail_count, last_fail_ts=excluded.last_fail_ts",
        (int(attacker_id), int(target_id), int(new_count), int(now_value)),
        commit=True
    )
    return int(new_count)

def _calc_infection_gain_with_fail_stack(target_bio_exp: int, fail_stack: int) -> int:
    base_gain = int(target_bio_exp or 0) // 2
    if base_gain < 1:
        base_gain = 1

    gained = float(base_gain)
    for _ in range(max(0, int(fail_stack or 0))):
        gained *= 0.9

    out = int(gained)
    if out < 1:
        out = 1
    return int(out)

def _fmt_clock_hms(ts: int) -> str:
    try:
        return time.strftime("%H:%M:%S", time.localtime(int(ts)))
    except Exception:
        return "00:00:00"

def kb_infect_retry_user(attacker_id: int, target_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("Попробовать ещё раз", callback_data=f"{INFUI_TAG}:U:{attacker_id}:{target_id}:1"),
    )
    kb.row(
        InlineKeyboardButton("× 2", callback_data=f"{INFUI_TAG}:U:{attacker_id}:{target_id}:2"),
        InlineKeyboardButton("× 5", callback_data=f"{INFUI_TAG}:U:{attacker_id}:{target_id}:5"),
        InlineKeyboardButton("× 10", callback_data=f"{INFUI_TAG}:U:{attacker_id}:{target_id}:10"),
    )
    return kb

def kb_infect_retry_mass(attacker_id: int, mode: str, chat_filter: str) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("Попробовать ещё раз", callback_data=f"{INFUI_TAG}:M:{attacker_id}:{mode}:{chat_filter}:1"),
    )
    kb.row(
        InlineKeyboardButton("× 2", callback_data=f"{INFUI_TAG}:M:{attacker_id}:{mode}:{chat_filter}:2"),
        InlineKeyboardButton("× 5", callback_data=f"{INFUI_TAG}:M:{attacker_id}:{mode}:{chat_filter}:5"),
        InlineKeyboardButton("× 10", callback_data=f"{INFUI_TAG}:M:{attacker_id}:{mode}:{chat_filter}:10"),
    )
    return kb

def kb_infect_retry_user_upg(attacker_id: int, target_id: int) -> InlineKeyboardMarkup:
    kb = kb_infect_retry_user(attacker_id, target_id)
    kb.row(
        _ikb_premium_lead(
            "🦠",
            "Усилить заразность × 1",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 1, "U", str(target_id)),
            style="success"
        )
    )
    kb.row(
        _ikb_premium_counter(
            "🦠",
            "× 2",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 2, "U", str(target_id)),
            style="success"
        ),
        _ikb_premium_counter(
            "🦠",
            "× 3",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 3, "U", str(target_id)),
            style="success"
        ),
        _ikb_premium_counter(
            "🦠",
            "× 5",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 5, "U", str(target_id)),
            style="success"
        ),
    )
    return kb

def _parse_infect_cb(data: str):
    try:
        parts = (data or "").split(":")
        if len(parts) < 2 or parts[0] != INFUI_TAG:
            return None
        kind = parts[1]
        if kind == "U" and len(parts) == 5:
            return {"kind": "U", "attacker": int(parts[2]), "target": int(parts[3]), "count": int(parts[4])}
        if kind == "M" and len(parts) == 6:
            return {"kind": "M", "attacker": int(parts[2]), "mode": parts[3], "filter": parts[4], "count": int(parts[5])}
    except Exception:
        return None
    return None

def _pick_target_from_db(attacker_id: int, mode: str, chat_id: int, chat_filter: str, exclude_ids: set[int]) -> Optional[int]:
    now = now_ts()
    if mode == "c":
        if chat_id == 0:
            return None
        sync_chat_admins(int(chat_id))

        att_exp_row = db_one("SELECT COALESCE(bio_exp,0) AS e FROM labs WHERE user_id=?", (int(attacker_id),))
        att_exp = int(att_exp_row["e"] if att_exp_row else 0)

        base = (
            "SELECT cm.user_id AS uid, COALESCE(l.bio_exp,0) AS be "
            "FROM chat_members cm "
            "LEFT JOIN labs l ON l.user_id = cm.user_id "
            "LEFT JOIN infection_cooldowns ic ON ic.attacker_id=? AND ic.target_id=cm.user_id "
            "WHERE cm.chat_id=? AND cm.user_id!=? AND cm.user_id>0 "
            "AND (ic.until_ts IS NULL OR ic.until_ts<=?)"
        )
        params = [int(attacker_id), int(chat_id), int(attacker_id), int(now)]
        if exclude_ids:
            base += " AND cm.user_id NOT IN (%s)" % (",".join(["?"] * len(exclude_ids)))
            params.extend(list(exclude_ids))

        if chat_filter == "p":
            base += " AND COALESCE(l.bio_exp,0) > ?"
            params.append(att_exp)
        elif chat_filter == "m":
            base += " AND COALESCE(l.bio_exp,0) < ?"
            params.append(att_exp)
        elif chat_filter == "e":
            base += " AND COALESCE(l.bio_exp,0) = ?"
            params.append(att_exp)

        rows = db_all(base, tuple(params)) or []
        rows = [r for r in rows if not same_corp(int(attacker_id), int(r["uid"]))]
        if not rows:
            return None

        if chat_filter == "p":
            mx = max(int(r["be"] or 0) for r in rows)
            top = [int(r["uid"]) for r in rows if int(r["be"] or 0) == mx]
            return random.choice(top)
        if chat_filter == "m":
            mn = min(int(r["be"] or 0) for r in rows)
            botm = [int(r["uid"]) for r in rows if int(r["be"] or 0) == mn]
            return random.choice(botm)
        if chat_filter == "e":
            eq = [int(r["uid"]) for r in rows if int(r["be"] or 0) == att_exp]
            if not eq:
                return None
            return random.choice(eq)

        return int(random.choice(rows)["uid"])

    att_exp_row = db_one("SELECT COALESCE(bio_exp,0) AS e FROM labs WHERE user_id=?", (int(attacker_id),))
    att_exp = int(att_exp_row["e"] if att_exp_row else 0)

    base = (
        "SELECT u.user_id AS uid, COALESCE(l.bio_exp,0) AS be "
        "FROM users u "
        "LEFT JOIN labs l ON l.user_id=u.user_id "
        "LEFT JOIN infection_cooldowns ic ON ic.attacker_id=? AND ic.target_id=u.user_id "
        "WHERE u.user_id!=? AND (ic.until_ts IS NULL OR ic.until_ts<=?)"
    )
    params = [int(attacker_id), int(attacker_id), int(now)]
    if exclude_ids:
        base += " AND u.user_id NOT IN (%s)" % (",".join(["?"] * len(exclude_ids)))
        params.extend(list(exclude_ids))

    if mode == "p":
        base += " AND COALESCE(l.bio_exp,0) > ?"
        params.append(att_exp)
    elif mode == "m":
        base += " AND COALESCE(l.bio_exp,0) < ?"
        params.append(att_exp)
    elif mode == "e":
        base += " AND COALESCE(l.bio_exp,0) = ?"
        params.append(att_exp)

    rows = db_all(base, tuple(params)) or []
    rows = [r for r in rows if not same_corp(int(attacker_id), int(r["uid"]))]
    if not rows:
        return None

    if mode == "r":
        return int(random.choice(rows)["uid"])

    if mode == "p":
        mx = max(int(r["be"] or 0) for r in rows)
        top = [int(r["uid"]) for r in rows if int(r["be"] or 0) == mx]
        return random.choice(top)

    if mode == "m":
        mn = min(int(r["be"] or 0) for r in rows)
        botm = [int(r["uid"]) for r in rows if int(r["be"] or 0) == mn]
        return random.choice(botm)

    if mode == "e":
        eq = [int(r["uid"]) for r in rows if int(r["be"] or 0) == att_exp]
        if not eq:
            return None
        return random.choice(eq)

    return None

def _parse_infect_request(message, parsed: "Parsed", attacker_id: int) -> dict:
    """
    Возвращает структуру запроса.
    kind="U": фикс-цель (reply/@/id/link)
    kind="M": массовое по переменной (р/+/-/= / чат)
    kind="NONE": нет цели (ошибка)

    Для фикс-цели новый формат:
      заразить 10 @user
      заразить 5 123456789
      заразить 3 https://t.me/username

    Reply-формат:
      reply + "заразить 10"
    """
    args = (parsed.args or "").strip()
    toks = args.split() if args else []

    if message.reply_to_message and is_channel_sender_message(message.reply_to_message):
        return {"kind": "NONE"}

    if message.reply_to_message:
        ru = getattr(message.reply_to_message, "from_user", None)

        if (
            ru
            and not bool(getattr(ru, "is_bot", False))
            and int(getattr(ru, "id", 0) or 0) != int(attacker_id)
        ):
            capture_user_context(message, ru)
            tid = int(ru.id)
            cnt = 1
            if toks and toks[0].isdigit():
                cnt = int(toks[0])
            return {"kind": "U", "target": tid, "count": cnt}

        tid = _pick_reply_target_id(message, exclude_user_ids={int(attacker_id)})
        if tid is not None:
            cnt = 1
            if toks and toks[0].isdigit():
                cnt = int(toks[0])
            return {"kind": "U", "target": int(tid), "count": cnt}

        if ru and not bool(getattr(ru, "is_bot", False)):
            capture_user_context(message, ru)
            tid = int(ru.id)
            cnt = 1
            if toks and toks[0].isdigit():
                cnt = int(toks[0])
            return {"kind": "U", "target": tid, "count": cnt}

    if not toks:
        return {"kind": "NONE"}

    if toks[0].lower() == "чат":
        cnt = 1
        flt = "n"
        if len(toks) >= 2 and toks[1].isdigit():
            cnt = int(toks[1])
        if len(toks) >= 3:
            flt = INF_CHAT_FILTER_SYNONYMS.get(toks[2].lower(), "n")
        return {"kind": "M", "mode": "c", "count": cnt, "filter": flt}

    if len(toks) >= 2 and toks[0].isdigit():
        cnt = int(toks[0])
        tid = _resolve_or_create_infect_target(toks[1])
        if tid is not None:
            return {"kind": "U", "target": int(tid), "token": toks[1], "count": cnt}

    tid0 = _resolve_or_create_infect_target(toks[0])
    if tid0 is not None:
        cnt = 1
        if len(toks) >= 2 and toks[1].isdigit():
            cnt = int(toks[1])
        return {"kind": "U", "target": int(tid0), "token": toks[0], "count": cnt}

    key = toks[0].lower()
    mode = INF_MODE_SYNONYMS.get(key)
    if mode and mode != "c":
        cnt = 1
        if len(toks) >= 2 and toks[1].isdigit():
            cnt = int(toks[1])
        return {"kind": "M", "mode": mode, "count": cnt, "filter": "n"}

    return {"kind": "NONE"}

#           горячка
def _calc_inf_days(lethality_level: int) -> int:
    try:
        raw = int(lethality_level or 0)
    except Exception:
        raw = 0
    lvl = max(0, raw - 1)
    days = int(INF_DAY) + lvl
    if days < 1:
        days = 1
    return int(days)

def _calc_fever_sec(lethality_level: int) -> int:
    try:
        raw = int(lethality_level or 0)
    except Exception:
        raw = 0
    lvl = max(0, raw - 1)
    
    add = (lvl // 2) * 60
    sec = int(FEVER_SEC) + int(add)

    if sec > FEVER_MAX_SEC:
        sec = FEVER_MAX_SEC
    if sec < 0:
        sec = 0
    return int(sec)

PATHOGEN_MIN_SEC = 60          # минимум 1 минута
VACCINE_MIN_SEC = 30 * 60      # минимум 30 минут

def _craft_params(base_sec: int, min_sec: int, acc_level: int) -> tuple[int, float]:
    try:
        acc = int(acc_level or 0)
    except Exception:
        acc = 0
    craft = int(base_sec) - (acc * 10)
    if craft < int(min_sec):
        craft = int(min_sec)

    cap = 0
    if int(base_sec) > int(min_sec):
        cap = (int(base_sec) - int(min_sec) + 9) // 10 
    extra = max(0, acc - cap)
    dup_pct = min(100.0, float(extra) * 0.1)
    return int(craft), float(dup_pct)

def _synth_bonus_value(syn_level: int) -> int:
    try:
        lvl = int(syn_level or 0)
    except Exception:
        lvl = 0
    if lvl < 1:
        lvl = 1
    return max(0, lvl - 1) * 10

def _roll_pct(pct: float) -> bool:
    try:
        return random.random() * 100.0 < float(pct)
    except Exception:
        return False

def _cb_buy_vaccine(uid: int) -> str:
    return f"{CB_BUY_VACCINE}:{int(uid)}"

def _cb_use_vaccine(uid: int) -> str:
    return f"{CB_USE_VACCINE}:{int(uid)}"

def _cb_use_vaccine_x(uid: int, doses: int) -> str:
    return f"{CB_USE_VACCINE_X}:{int(uid)}:{int(doses)}"

VACCINE_FAIL_TEXT = (
    "🧿 Вакцина не смогла справиться с болезнью. Патоген оказался устойчивее к антителам вакцины.\n"
    "Введите повторную дозу или отлежитесь какое-то время."
)

#           улучшение
SKILL_N1 = {
    "INF": 7,   # заразность
    "LET": 4,   # летальность
    "HEA": 10,  # тяжесть
    "IMM": 7,   # иммунитет
    "REA": 6,   # реагирование
    "IDS": 5,   # обнаружение
    "IPS": 7,   # предотвращение
    "SYN": 15,  # синтез
    "ACC": 5,   # ускоренное производство
    "PAT": 4,   # патогены
    "VAC": 8,   # вакцины
}

SKILLS = {
    "INF": {"col": "infectivity", "title_1": "Усиление заразности патогена", "title_2": "заразность", "emoji": "🦠"},
    "LET": {"col": "lethality",   "title_1": "Усиление летальности патогена", "title_2": "летальность", "emoji": "☠️"},
    "HEA": {"col": "heaviness",   "title_1": "Усиление тяжести патогена", "title_2": "тяжесть", "emoji": "🧿"},
    "IMM": {"col": "immunity",    "title_1": "Усиление иммунитета", "title_2": "иммунитет", "emoji": "🛡"},
    "REA": {"col": "reaction",    "title_1": "Улучшение оборудования группы быстрого реагирования", "title_2": "реагирование", "emoji": "👮"},
    "IDS": {"col": "ids",         "title_1": "Улучшение системы обнаружения угроз", "title_2": "обнаружение", "emoji": "🛰️"},
    "IPS": {"col": "ips",         "title_1": "Улучшение системы предотвращения угроз", "title_2": "предотвращение", "emoji": "📟"},
    "SYN": {"col": "synthesis",   "title_1": "Улучшение химического оборудования", "title_2": "синтез", "emoji": "⚗️"},
    "ACC": {"col": "acceleration","title_1": "Улучшение лабораторного оборудования", "title_2": "ускорение", "emoji": "🧫"},
    "PAT": {"col": "total_pathogens", "ready_col": "ready_pathogens", "title_1": "Увеличение количества ячеек патогенов", "title_2": "патоген", "emoji": "🧪"},
    "VAC": {"col": "total_vaccines",  "ready_col": "ready_vaccines",  "title_1": "Увеличение количества ячеек вакцин", "title_2": "вакцина",  "emoji": "💉"},
}

SKILL_SYNONYMS = {
    "заразность": "INF", "заразн": "INF",
    "летальность": "LET", "летал": "LET",
    "тяжесть": "HEA", "тяж": "HEA",
    "иммунитет": "IMM", "иммун": "IMM",
    "реагирование": "REA", "реаг": "REA",
    "обнаружение": "IDS", "обнаруж": "IDS", "ids": "IDS",
    "предотвращение": "IPS", "предотв": "IPS", "ips": "IPS",
    "синтез": "SYN", "синт": "SYN",
    "ускорение": "ACC", "ускор": "ACC", "производство": "ACC",
    "патоген": "PAT", "патогены": "PAT",
    "вакцина": "VAC", "вакцины": "VAC",
}

def _ru_dots(n: int) -> str:
    return _fmt_groups_dots(_split_3_groups(int(n)))

def _level_price(n1: int, level: int) -> int:
    level = int(level)
    if level <= 1:
        return 0
    k = int(level) - 1
    base = int(n1)
    a = 2 * base + 6
    b = base - 3
    return int(base + a * (k - 1) + b * ((k - 1) * k) // 2)

def _upgrade_cost(n1: int, cur_level: int, steps: int) -> int:
    cur_level = int(cur_level)
    steps = int(steps)
    if steps <= 0:
        return 0
    total = 0
    for lvl in range(cur_level + 1, cur_level + steps + 1):
        total += _level_price(n1, lvl)
    return int(total)

def _calc_cost_range(n1: int, from_level: int, to_level: int) -> int:
    from_level = int(from_level)
    to_level = int(to_level)
    if to_level <= from_level:
        return 0
    total = 0
    for lvl in range(from_level + 1, to_level + 1):
        total += _level_price(n1, lvl)
    return int(total)

def _avg_skill_level(uid: int) -> float:
    ensure_lab_exists(int(uid))

    cols = [
        "infectivity", "lethality", "heaviness", "immunity",
        "reaction", "ids", "ips", "acceleration",
        "total_pathogens", "total_vaccines",
    ]

    select_sql = ", ".join([f"COALESCE({c},1) AS {c}" for c in cols])
    row = db_one(f"SELECT {select_sql} FROM labs WHERE user_id=?", (int(uid),))

    if not row:
        return 1.0

    vals = []
    for c in cols:
        try:
            vals.append(max(1, int(row[c] or 1)))
        except Exception:
            vals.append(1)

    return float(sum(vals)) / float(len(vals))

def get_vaccine_price(uid: int) -> int:
    avg_lvl = _avg_skill_level(int(uid))
    add_steps = int(avg_lvl // VACCINE_PRICE_EVERY_AVG_LVLS)
    price = VACCINE_PRICE_BASE + add_steps * VACCINE_PRICE_STEP
    return min(int(price), int(VACCINE_PRICE_MAX))

def _resolve_skill(token: str) -> Optional[str]:
    t = (token or "").strip().lower()
    if not t:
        return None
    if t in SKILLS:
        return t
    return SKILL_SYNONYMS.get(t)

def _recalc_derived(uid: int):
    row = db_one(
        "SELECT COALESCE(reaction,1) AS r, COALESCE(ids,1) AS i, COALESCE(ips,1) AS p, "
        "COALESCE(total_pathogens,1) AS tp, COALESCE(total_vaccines,1) AS tv, COALESCE(acceleration,1) AS a "
        "FROM labs WHERE user_id=?",
        (int(uid),)
    )
    if not row:
        return
    sec = (int(row["r"]) + int(row["i"]) + int(row["p"])) // 3
    qual = (int(row["tp"]) + int(row["tv"]) + int(row["a"])) // 3
    db_exec("UPDATE labs SET security=?, qualification=? WHERE user_id=?", (int(sec), int(qual), int(uid)), commit=True)

SABOTAGE_DOWNGRADE_CODES = (
    "INF", "LET", "HEA", "IMM",
    "REA", "IDS", "IPS", "SYN", "ACC",
    "PAT", "VAC",
)

def _sabotage_reward_from_target(target_res: int, target_mat: int) -> tuple[str, int]:
    tr = max(0, int(target_res or 0))
    tm = max(0, int(target_mat or 0))

    if tm > 0:
        return "mat", max(1, int(math.ceil(tm * 0.10)))
    if tr > 0:
        return "res", max(1, int(math.ceil(tr * 0.10)))
    return "bonus_mat", 1

def _sabotage_reward_text(kind: str, amount: int) -> str:
    amt = max(1, int(amount or 1))
    if str(kind or "") == "res":
        return _fmt_bio_res(amt)
    return _fmt_bio_mater(amt)

def _pay_cost(uid: int, cost: int):
    cost = int(cost)
    if cost <= 0:
        return True, 0, 0
    row = db_one(
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m FROM labs WHERE user_id=?",
        (int(uid),)
    )
    have_r = int(row["r"] if row else 0)
    have_m = int(row["m"] if row else 0)
    if have_r + have_m < cost:
        return False, 0, 0

    spent_r = min(have_r, cost)
    spent_m = cost - spent_r

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "UPDATE labs SET all_bio_res=CASE WHEN COALESCE(all_bio_res,0) >= ? THEN all_bio_res-? ELSE 0 END, "
                "all_bio_mater=CASE WHEN COALESCE(all_bio_mater,0) >= ? THEN all_bio_mater-? ELSE 0 END "
                "WHERE user_id=?",
                (spent_r, spent_r, spent_m, spent_m, int(uid))
            )
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try: c.close()
            except Exception: pass

    return True, int(spent_r), int(spent_m)

def _upg_cb(action: str, uid: int, code: str, steps: int, src: str = "C") -> str:
    src = (src or "C")
    if src not in ("C", "D", "I", "PB"):
        src = "C"
    return f"{UPGUI_TAG}:{action}:{int(uid)}:{code}:{int(steps)}:{src}"

def _upg_cb_i(action: str, uid: int, code: str, steps: int, ictype: str, *ctx: str) -> str:
    base = _upg_cb(action, uid, code, steps, "I")
    extra = ":".join([ictype] + [str(x) for x in ctx if x is not None])
    return f"{base}:{extra}"

def _upg_cb_parse(data: str):
    try:
        p = (data or "").split(":")
        if len(p) < 5 or p[0] != UPGUI_TAG:
            return None
        info = {"action": p[1], "uid": int(p[2]), "code": p[3], "steps": int(p[4])}
        info["src"] = p[5] if len(p) >= 6 else "C"
        if info["src"] not in ("C", "D", "I", "PB"):
            info["src"] = "C"
        if len(p) >= 8:
            info["ictype"] = p[6]
            info["ictx"] = p[7:]
        return info
    except Exception:
        return None

def kb_upgrade(uid: int, code: str, steps: int, src: str = "C", ictype: Optional[str] = None, ictx: Optional[list[str]] = None) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()

    def _cb(action: str, s: int) -> str:
        if src == "I" and ictype:
            ctx = ictx or []
            return _upg_cb_i(action, uid, code, s, ictype, *ctx)
        return _upg_cb(action, uid, code, s, src)

    kb.row(InlineKeyboardButton("Подтвердить улучшение", callback_data=_cb("B", int(steps))))
    kb.row(
        InlineKeyboardButton("× 1", callback_data=_cb("P", 1)),
        InlineKeyboardButton("× 2", callback_data=_cb("P", 2)),
        InlineKeyboardButton("× 5", callback_data=_cb("P", 5)),
    )
    sp_row = db_one("SELECT COALESCE(skill_points,0) AS sp FROM labs WHERE user_id=?", (int(uid),))
    sp = int(sp_row["sp"] or 0) if sp_row else 0
    if sp > 0:
        kb.row(
            _ikb_premium_lead(
                "🔹",
                f"Использовать очко навыка из {sp}",
                callback_data=_cb("SP", 1),
                style="primary"
            )
        )
    return kb

def _upgrade_skill_points_count(uid: int) -> int:
    row = db_one(
        "SELECT COALESCE(skill_points,0) AS sp FROM labs WHERE user_id=?",
        (int(uid),)
    )
    return int(row["sp"] or 0) if row else 0

def _upgrade_chain_cb(action: str, uid: int, code: str, steps: int, src: str = "C", ictype: Optional[str] = None, ictx: Optional[list[str]] = None) -> str:
    if src == "I" and ictype:
        ctx = ictx or []
        return _upg_cb_i(action, int(uid), str(code), int(steps), str(ictype), *ctx)
    return _upg_cb(action, int(uid), str(code), int(steps), str(src or "C"))

def _upgrade_shortage_text(uid: int) -> str:
    row = db_one(
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m, COALESCE(skill_points,0) AS sp "
        "FROM labs WHERE user_id=?",
        (int(uid),)
    )
    have_r = int(row["r"] or 0) if row else 0
    have_m = int(row["m"] or 0) if row else 0
    sp = int(row["sp"] or 0) if row else 0

    if sp > 0:
        pts_word = _ru_form(sp, "очко навыка", "очка навыка", "очков навыка")
        return (
            "📝 У вас нет столько био-ресурсов или био-материалов.\n"
            f"Однако, на вашем счету имеется 🔹 {_fmt_k(sp)} {pts_word}. Хотите использовать?"
        )

    if have_r <= 0 and have_m <= 0:
        return "📝 У вас нет столько био-ресурсов или био-материалов, или очков навыков."

    return "📝 У вас нет столько био-ресурсов или био-материалов."

def kb_upgrade_shortage(
    uid: int,
    code: str,
    steps: int,
    src: str = "C",
    ictype: Optional[str] = None,
    ictx: Optional[list[str]] = None,
    *,
    include_balance: bool = True
) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)

    sp = _upgrade_skill_points_count(int(uid))
    row_btns = []

    if sp > 0:
        row_btns.append(
            _ikb_premium_lead(
                "🔹",
                "Использовать 1",
                callback_data=_upgrade_chain_cb("SP", uid, code, steps, src, ictype, ictx),
                style="primary"
            )
        )

    if include_balance:
        row_btns.append(
            InlineKeyboardButton("Баланс", callback_data=_balui_data(int(uid), "B"), style="primary")
        )

    if row_btns:
        kb.row(*row_btns)

    return kb

def _upgrade_balance_payload(code: str, steps: int, src: str = "C", ictype: Optional[str] = None, ictx: Optional[list[str]] = None) -> dict:
    return {
        "code": str(code or "").strip().upper(),
        "steps": int(max(1, steps or 1)),
        "src": str(src or "C"),
        "ictype": str(ictype or ""),
        "ictx": list(ictx or []),
    }

def _upgrade_payload_parts(payload: dict) -> tuple[str, int, str, Optional[str], list[str]]:
    p = payload if isinstance(payload, dict) else {}
    code = str(p.get("code") or "").strip().upper()
    steps = max(1, int(p.get("steps") or 1))
    src = str(p.get("src") or "C").strip() or "C"
    ictype = str(p.get("ictype") or "").strip() or None
    ictx = list(p.get("ictx") or [])
    return code, steps, src, ictype, ictx

def _append_upgrade_return_buttons(rm: Optional[InlineKeyboardMarkup], uid: int, src: str, ictype: Optional[str] = None, ictx: Optional[list[str]] = None) -> Optional[InlineKeyboardMarkup]:
    if rm is None:
        return None

    if src == "D":
        rm.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D"), style="primary"))
    elif src == "PB":
        rm.row(InlineKeyboardButton("Вернуться к сводке", callback_data=_pathogens_ui_data(uid, "INFO", 0), style="primary"))

    return rm

def _append_balance_return_buttons(kb: Optional[InlineKeyboardMarkup], uid: int) -> Optional[InlineKeyboardMarkup]:
    if kb is None:
        kb = InlineKeyboardMarkup()

    state = get_balance_chain_state(int(uid))
    if not state:
        return kb

    kind = str(state.get("chain_kind") or "").strip()
    payload = state.get("payload") or {}

    src = ""
    if kind == BALCHAIN_UPGRADE:
        _code, _steps, src, _ictype, _ictx = _upgrade_payload_parts(payload)

    if src == "D":
        kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(int(uid), "D"), style="primary"))
    elif src == "PB":
        kb.row(InlineKeyboardButton("Вернуться к сводке", callback_data=_pathogens_ui_data(int(uid), "INFO", 0), style="primary"))

    return kb

def _kb_balance_upgrade_actions(uid: int, state: dict, *, from_synth: bool = False) -> Optional[InlineKeyboardMarkup]:
    payload = (state or {}).get("payload") or {}
    code, steps, src, ictype, ictx = _upgrade_payload_parts(payload)
    if code not in SKILLS:
        return None

    kb = InlineKeyboardMarkup(row_width=2)

    sp = _upgrade_skill_points_count(int(uid))
    can_repeat, repeat_text = _balance_chain_can_resume(int(uid), state)

    row_btns = []
    if sp > 0:
        row_btns.append(
            _ikb_premium_lead(
                "🔹",
                "Использовать 1",
                callback_data=_upgrade_chain_cb("SP", uid, code, steps, src, ictype, ictx),
                style="primary"
            )
        )

    if can_repeat and repeat_text:
        row_btns.append(
            _balance_chain_upgrade_button(
                code,
                steps,
                callback_data=_balui_data(int(uid), "R", "U"),
                style="primary"
            )
        )

    if row_btns:
        kb.row(*row_btns)

    if synth_left_seconds(uid) <= 0:
        kb.add(_ikb_premium_counter("⚗️", "Синтез", callback_data=_balui_data(uid, "S")))

    return kb if getattr(kb, "keyboard", None) else None

def _build_upgrade_preview(uid: int, code: str, steps: int) -> str:
    ensure_lab_exists(int(uid))
    lab = get_lab(int(uid))
    skill = SKILLS[code]
    n1 = SKILL_N1[code]
    cur = int(_rget(lab, skill["col"], 1) or 1)
    steps = max(1, min(5, int(steps)))
    final_lvl = cur + steps
    price = _upgrade_cost(n1, cur, steps)

    extra_lines = ""
    if code == "ACC":
        bp, _ = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, cur)
        ap, _ = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, final_lvl)
        bv, _ = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, cur)
        av, _ = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, final_lvl)
        if bp != ap:
            extra_lines += f"🧪 Время произв.: {_format_hms(bp)} → {_format_hms(ap)}\n"
        if bv != av:
            extra_lines += f"💉 Время произв.: {_format_hms(bv)} → {_format_hms(av)}\n"

    if code == "SYN":
        bsyn = _synth_bonus_value(cur)
        add_syn = _synth_bonus_value(final_lvl) - bsyn
        extra_lines += f"📈 Рост эффективности: {bsyn} + {add_syn}\n"

    if code == "LET":
        bfev = _calc_fever_sec(cur)
        afev = _calc_fever_sec(final_lvl)
        if bfev != afev and afev < FEVER_MAX_SEC and bfev < FEVER_MAX_SEC:
            extra_lines += f"🌡️ Горячка: {_format_hm_from_seconds(bfev)} → {_format_hm_from_seconds(afev)}\n"

    if code == "IPS":
        bauto = _auto_limit_from_ips(cur)
        aauto = _auto_limit_from_ips(final_lvl)
        if bauto != aauto:
            extra_lines += f"🤖 Автоответы: {bauto} → {aauto}\n"

    return (
        f"{skill['emoji']} {h(skill['title_1'])} на {steps} ур ({final_lvl})\n"
        f"{extra_lines}"
        f"🏷️ Цена: 🧬 <b>{_ru_dots(price)}</b> ({_fmt_k(price)})\n\n"
        f"💬 Чтобы подтвердить усиление навыка, введите команду \"<code>Био ++{h(skill['title_2'])} {steps}</code>\""
    )

def _execute_upgrade(uid: int, code: str, steps: int):
    ensure_lab_exists(int(uid))
    lab = get_lab(int(uid))
    skill = SKILLS[code]
    n1 = SKILL_N1[code]
    col = skill["col"]

    cur = int(_rget(lab, col, 1) or 1)
    steps = max(1, min(5, int(steps)))
    final_lvl = cur + steps
    price = _upgrade_cost(n1, cur, steps)

    extra_lines = ""
    if code == "ACC":
        bp, _ = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, cur)
        ap, _ = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, final_lvl)
        bv, _ = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, cur)
        av, _ = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, final_lvl)
        if bp != ap:
            extra_lines += f"🧪 Время произв.: {_format_hms(bp)} → {_format_hms(ap)}\n"
        if bv != av:
            extra_lines += f"💉 Время произв.: {_format_hms(bv)} → {_format_hms(av)}\n"

    if code == "SYN":
        bsyn = _synth_bonus_value(cur)
        add_syn = _synth_bonus_value(final_lvl) - bsyn
        extra_lines += f"📈 Рост эффективности: {bsyn} + {add_syn}\n"

    ok, spent_r, spent_m = _pay_cost(int(uid), price)
    if not ok:
        return False, "📝 У вас нет столько био-ресурсов или био-материалов.", None

    extra_updates = ""
    params = []

    if code in ("PAT", "VAC"):
        ready_col = skill.get("ready_col")
        extra_updates = f", {ready_col}={ready_col}+?"
        params.append(int(steps))

    params.extend([int(steps), int(uid)])
    db_exec(f"UPDATE labs SET {col}={col}+?{extra_updates} WHERE user_id=?", tuple(params), commit=True)

    _recalc_derived(int(uid))

    if spent_r > 0 and spent_m > 0:
        spent_txt = f"🧾 Потрачено 🧬 {_fmt_k(spent_r)} + 💊 {_fmt_k(spent_m)}"
    elif spent_r > 0:
        spent_txt = f"🧾 Потрачено 🧬 {_fmt_k(spent_r)}"
    else:
        spent_txt = f"🧾 Потрачено 💊 {_fmt_k(spent_m)}"

    text = (
        f"✅ {h(skill['title_1'])} выполнено на {cur} ур ({final_lvl})\n"
        f"{extra_lines}"
        f"{spent_txt}\n\n"
        "Дополнительно:"
    )
    return True, text, final_lvl

def _execute_upgrade_by_skill_point(uid: int, code: str):
    ensure_lab_exists(int(uid))
    if code not in SKILLS:
        return False, "📑 Навык не найден.", None

    row = db_one("SELECT COALESCE(skill_points,0) AS sp FROM labs WHERE user_id=?", (int(uid),))
    sp = int(row["sp"] or 0) if row else 0
    if sp <= 0:
        return False, "📝 У вас нет очков навыка.", None

    skill = SKILLS[code]
    col = skill["col"]
    cur_row = db_one(f"SELECT COALESCE({col},1) AS v FROM labs WHERE user_id=?", (int(uid),))
    cur = int(cur_row["v"] or 1) if cur_row else 1
    final_lvl = cur + 1

    db_exec(
        f"UPDATE labs SET {col}=COALESCE({col},1)+1, skill_points=CASE WHEN COALESCE(skill_points,0)>0 THEN skill_points-1 ELSE 0 END WHERE user_id=?",
        (int(uid),),
        commit=True
    )
    _recalc_derived(int(uid))

    extra_lines = ""
    if code == "SYN":
        bsyn = _synth_bonus_value(cur)
        add_syn = _synth_bonus_value(final_lvl) - bsyn
        extra_lines += f"📈 Рост эффективности: {bsyn} + {add_syn}\n"
    if code == "ACC":
        bp, bdup = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, cur)
        ap, adup = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, final_lvl)
        bv, bdupv = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, cur)
        av, adupv = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, final_lvl)
        if bp != ap:
            extra_lines += f"🧪 Время произв.: {_format_hms(bp)} → {_format_hms(ap)}\n"
        elif adup != bdup:
            extra_lines += f"🧪 Дублирование: {_fmt_pct_text(bdup)} → {_fmt_pct_text(adup)}\n"
        if bv != av:
            extra_lines += f"💉 Время произв.: {_format_hms(bv)} → {_format_hms(av)}\n"
        elif adupv != bdupv:
            extra_lines += f"💉 Дублирование: {_fmt_pct_text(bdupv)} → {_fmt_pct_text(adupv)}\n"

    text = (
        f"✅ {h(skill['title_1'])} выполнено на {cur} ур ({final_lvl})\n"
        f"{extra_lines}"
        "🔹 Потрачено 1 очко навыка"
    )
    return True, text, final_lvl

def handle_upgrade_command(message, parsed: Parsed, edit_ctx: Optional[dict] = None, actor_user=None):
    actor = actor_user or message.from_user
    uid = int(actor.id)
    upsert_user(actor)
    ensure_lab_exists(uid)
    mark_lab_active(uid)

    def _emit(text: str, reply_markup=None):
        if edit_ctx and isinstance(edit_ctx, dict):
            inline_id = edit_ctx.get("inline_id")
            chat_id = edit_ctx.get("chat_id")
            msg_id = edit_ctx.get("msg_id")
            if inline_id:
                limited_edit_message_text(text=text, inline_id=inline_id, parse_mode="HTML",
                                          reply_markup=reply_markup, disable_web_page_preview=True)
                return
            if chat_id and msg_id:
                limited_edit_message_text(text=text, chat_id=chat_id, msg_id=msg_id, parse_mode="HTML",
                                          reply_markup=reply_markup, disable_web_page_preview=True)
                return
        bot.reply_to(message, text, disable_web_page_preview=True, reply_markup=reply_markup)

    parts = (parsed.args or "").strip().split()
    if not parts:
        return

    code = _resolve_skill(parts[0])
    if not code or code not in SKILLS:
        return

    steps = 1
    if len(parts) >= 2 and parts[1].isdigit():
        steps = int(parts[1])
    steps = max(1, min(5, steps))

    if parsed.cmd == "upgrade_preview":
        _emit(_build_upgrade_preview(uid, code, steps), reply_markup=kb_upgrade(uid, code, steps, "C"))
        return

    ok, txt, _final = _execute_upgrade(uid, code, steps)
    if ok:
        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_UPGRADE:
            clear_balance_chain_state(int(uid))
        _emit(txt, reply_markup=kb_upgrade(uid, code, steps, "C"))
    else:
        set_balance_chain_state_from_message(
            message,
            BALCHAIN_UPGRADE,
            _balance_chain_upgrade_button_text(code, steps),
            _upgrade_balance_payload(code, steps, "C")
        )

        fail_text = _upgrade_shortage_text(int(uid))
        rm = kb_upgrade_shortage(int(uid), code, int(steps), "C", include_balance=True) if _upgrade_skill_points_count(int(uid)) > 0 else kb_open_balance(int(uid))
        _emit(fail_text, reply_markup=rm)

CALC_UPGRADE_MODE_ALIASES = {"улучшение", "улучшения", "улучш", "у", 
                             "прокачка", "прокачки", "прокач", "пк"}
CALC_CHANCE_MODE_ALIASES = {"шанс", "шанса", "шансы", "шансов", "ш", 
                            "проценты", "процента", "процентов", "процент", "проц", "пц"}
CALC_BUFF_MODE_ALIASES = {"усиление", "усиления", "усилений", "кс", "кус"}
CALC_EXP_MODE_ALIASES = {"опыт", "опыта", "о", "ко"}
CALC_DUEL_MODE_ALIASES = {"дуэль", "дуэли", "д", "кдл"}

CALC_CHANCE_METRIC_ALIASES = {
    "заражения": "INFECT", "заражение": "INFECT", "зар": "INFECT",
    "обнаружения": "IDS", "обнаружение": "IDS", "обн": "IDS", "ids": "IDS",
    "диверсии": "SAB", "диверсия": "SAB", "див": "SAB",
    "тяжести": "HEA", "тяжесть": "HEA", "тяж": "HEA",
}

CALC_BUFF_METRIC_ALIASES = {
    "синтез": "SYN", "синтеза": "SYN", "синт": "SYN",
    "ускорение": "ACC", "ускорения": "ACC", "ускор": "ACC", "ускр": "ACC",
    "летальность": "FEV", "летальности": "FEV", "летальн": "FEV", "летал": "FEV",
}

STRICT_NO_EXTRA_ARGS_CMDS = {
    "help", "commands_link", "report", "settings", "ping",
    "autoanswer_status", "autoanswer_on", "autoanswer_off",
    "buy_vaccine",
    "lab_delete", "restore_lab",
    "corp_delete", "corp_open", "corp_close",
    "corp_req_list", "corp_leave", "corp_my",
    "rp_stats",
    "blacklist", "users_list", "agents_panel",
    "my_owner", "my_owner_remove",
    "synth",
    "balance_show", "balance_hide", "lab_show", "lab_hide",
    "notify_on", "notify_off",
    "corp_notify_on", "corp_notify_off",
    "rp_on", "rp_off",
    "promo_generate", "promo_all",
    "chat_autodel_status", "chat_autodel_off",
    "timer_list", "timer_clear_all",
    "cof_inf_stats",
    "chatname_clear",
    "duel_accept", "duel_decline", "duel_cancel",
    "duel_fire", "duel_aim", "duel_break_aim", "duel_surrender",
    "duel_bets_list", "duel_stats",
}

CALC_MAIN_PUBLIC_VARS = [
    "улучшения",
    "усиления",
    "шансов",
    "опыта",
    "дуэли",
]

CALC_UPGRADE_PUBLIC_VARS = [
    "заразность",
    "летальность",
    "тяжесть",
    "иммунитет",
    "реагирование",
    "обнаружение",
    "предотвращение",
    "синтез",
    "ускорение",
    "патоген",
    "вакцина",
]

CALC_CHANCE_PUBLIC_VARS = [
    "заражения", 
    "обнаружения", 
    "диверсии", 
    "тяжести",
]

CALC_BUFF_PUBLIC_VARS = [
    "синтез", 
    "ускорение", 
    "летальность",
]

CALC_EXP_PUBLIC_VARS = [
    "опыт",
    "опыта",
]

CALC_DUEL_PUBLIC_VARS = [
    "дуэль",
    "дуэли",
]

def _calc_inline_hint_keyboard(prefix: str):
    kb = InlineKeyboardMarkup()
    kb.add(
        InlineKeyboardButton(
            "Подставить в строку ввода",
            switch_inline_query_current_chat=str(prefix or "").strip()
        )
    )
    return kb

def _calc_inline_error_text(mode_label: str, hint_text: str) -> str:
    return (
        "🧮 Калькулятор: При вводе параметров вы допустили ошибки синтаксиса. Попробуйте повторить запрос.\n"
        f"{hint_text}"
    )

def _calc_quote_block(lines: list[str]) -> str:
    body = "\n".join([h(x) for x in (lines or []) if str(x).strip()])
    return f"<blockquote>{body}</blockquote>" if body else ""

def _calc_main_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_MAIN_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для калькулятора:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_upgrade_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_UPGRADE_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для подсчёта улучшений:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_upgrade_levels_hint_text() -> str:
    return _calc_quote_block([
        "1. Укажите начальный и конечный уровни навыка.",
        "2. Соблюдайте условие: конечный уровень > начального уровня.",
    ])

def _calc_chance_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_CHANCE_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для подсчёта шансов:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_chance_metric_prompt_text(metric_key: str) -> str:
    metric_key = str(metric_key or "").strip().upper()
    if metric_key == "INFECT":
        return _calc_quote_block([
            "Укажите 1.уровень заразности 2.уровень иммунитета."
        ])
    if metric_key == "IDS":
        return _calc_quote_block([
            "Укажите 1.уровень IDS атакующего 2.уровень IDS защищающегося."
        ])
    if metric_key == "SAB":
        return _calc_quote_block([
            "Укажите 1.уровень группы быстрого реагирования атакующего 2.уровень IDS защищающегося."
        ])
    if metric_key == "HEA":
        return _calc_quote_block([
            "Укажите 1.уровень тяжести 2.уровень квалификации учёных."
        ])
    return ""

def _calc_buff_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_BUFF_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для подсчёта усилений:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_buff_levels_hint_text() -> str:
    return _calc_quote_block([
        "1. Укажите начальный и конечный уровни навыка.",
        "2. Соблюдайте условие: конечный уровень > начального уровня.",
    ])

def _calc_exp_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_EXP_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для подсчёта био-опыта:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_exp_levels_hint_text() -> str:
    return _calc_quote_block([
        "1. Укажите общее число био-опыта цели.",
        "2. Укажите число иммунных неудачных попыток заражения.",
    ])

def _calc_duel_hint_text() -> str:
    vars_txt = "\n".join([f"<code>{h(x)}</code>" for x in CALC_DUEL_PUBLIC_VARS])
    return (
        "📋 Доступные переменные для подсчёта дуэли:\n"
        "<blockquote expandable>"
        f"{vars_txt}\n"
        "</blockquote>"
    )

def _calc_duel_levels_hint_text() -> str:
    return _calc_quote_block([
        "1. Укажите число стаков прицеливания.",
        "2. Значение не может быть отрицательным.",
    ])

def _calc_join_prefix(parts: list[str]) -> str:
    return " ".join([str(x).strip() for x in (parts or []) if str(x).strip()]).strip()

def _fmt_pct_text(v: float) -> str:
    x = float(v)
    s = f"{x:.2f}".rstrip("0").rstrip(".")
    s = s.replace(".", ",")
    return f"{s}%"

def _calc_sabotage_success_pct(reaction_level: int, ips_level: int) -> float:
    g = max(0.0, float(int(reaction_level or 0)))
    s = max(0.0, float(int(ips_level or 0)))

    if g <= 0.0 and s <= 0.0:
        return 40.0

    den = g + s
    if den <= 0.0:
        return 0.0

    g_pct = (100.0 * g) / den
    s_pct = (100.0 * s) / den
    delta = g_pct - s_pct

    p = max(0.0, min(80.0, 40.0 + delta))
    return float(p)

# шансы тяжести
def _calc_heaviness_success_fail_pct(heaviness_level: int, qualification_level: int) -> tuple[float, float]:
    t = max(1.0, float(int(heaviness_level or 0)))
    q = max(1.0, float(int(qualification_level or 0)))

    p_success = min(60.0, max(10.0, 35.0 + ((t / q) * 100.0 - 100.0)))
    p_fail = 100.0 - p_success
    return float(p_success), float(p_fail)

def _calc_chance_payload(metric_token: str, lvl1: int, lvl2: int):
    metric_key = CALC_CHANCE_METRIC_ALIASES.get((metric_token or "").strip().lower())
    if not metric_key:
        return None

    l1 = int(lvl1)
    l2 = int(lvl2)

    if metric_key == "INFECT":
        success = float(infect_success_chance(l1, l2))
        fail = 100.0 - success
        label = "заражения"
        levels_txt = f"🦠 {l1} ур → 🛡️ {l2} ур"
    elif metric_key == "IDS":
        success = float(ids_report_pct(l1, l2))
        fail = 100.0 - success
        label = "обнаружения"
        levels_txt = f"\n🛰️ защита {l1} ур \n🛰️ нападение {l2} ур"
    elif metric_key == "SAB":
        success = float(_calc_sabotage_success_pct(l1, l2))
        fail = 100.0 - success
        label = "диверсии"
        levels_txt = f"👮 {l1} ур → 📟 {l2} ур"
    else:
        success, fail = _calc_heaviness_success_fail_pct(l1, l2)
        label = "тяжести"
        levels_txt = f"🧿 {l1} ур → 👨‍🔬 {l2} ур"

    return {
        "metric_key": metric_key,
        "label": label,
        "levels_txt": levels_txt,
        "success": success,
        "fail": fail,
        "text": (
            f"🧮 Калькулятор: 📊 Шансы {label} {levels_txt}\n"
            f"✅ Успех: <b>{_fmt_pct_text(success)}</b>\n"
            f"❌ Провал: <b>{_fmt_pct_text(fail)}</b>"
        )
    }

def _calc_buff_payload(metric_token: str, lvl1: int, lvl2: int):
    key = CALC_BUFF_METRIC_ALIASES.get((metric_token or "").strip().lower())
    if not key:
        return None

    n1 = int(lvl1)
    n2 = int(lvl2)
    if n1 >= n2:
        return None

    if key == "SYN":
        b1 = _synth_bonus_value(n1)
        b2 = _synth_bonus_value(n2)
        return {
            "text": (
                f"🧮 Калькулятор: ⚗️ Усиления синтеза <b>{n1}</b> → <b>{n2}</b>\n"
                f"📈 Постоянный бонус: <b>{b1}</b> → <b>{b2}</b>\n"
                f"🎲 Диапазон базового значения: <b>1</b>..<b>{100 + b1}</b> → <b>1</b>..<b>{100 + b2}</b>"
            )
        }

    if key == "FEV":
        f1 = _calc_fever_sec(n1)
        f2 = _calc_fever_sec(n2)
        return {
            "text": (
                f"🧮 Калькулятор: ☠️ Усиления летальности <b>{n1}</b> → <b>{n2}</b>\n"
                f"🌡️ Горячка: <b>{_format_hm_from_seconds(f1)}</b> → <b>{_format_hm_from_seconds(f2)}</b>"
            )
        }

    pp1, dup1 = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, n1)
    pp2, dup2 = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, n2)
    vv1, vdup1 = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, n1)
    vv2, vdup2 = _craft_params(VACCINE_CRAFT_SEC, VACCINE_MIN_SEC, n2)

    lines = [f"🧮 Калькулятор: 🧫 Усиления ускорения <b>{n1}</b> → <b>{n2}</b>"]

    if pp1 != pp2:
        lines.append(f"🧪 Время патогена: <b>{_format_hms(pp1)}</b> → <b>{_format_hms(pp2)}</b>")
    elif dup1 != dup2:
        lines.append(f"🧪 Дублирование патогена: <b>{_fmt_pct_text(dup1)}</b> → <b>{_fmt_pct_text(dup2)}</b>")

    if vv1 != vv2:
        lines.append(f"💉 Время вакцины: <b>{_format_hms(vv1)}</b> → <b>{_format_hms(vv2)}</b>")
    elif vdup1 != vdup2:
        lines.append(f"💉 Дублирование вакцины: <b>{_fmt_pct_text(vdup1)}</b> → <b>{_fmt_pct_text(vdup2)}</b>")

    return {"text": "\n".join(lines)}

def _calc_exp_payload(total_bio_exp: int, fail_count: int):
    total = max(0, int(total_bio_exp or 0))
    fails = max(0, int(fail_count or 0))

    base_gain = max(1, total // 2)
    final_gain = int(_calc_infection_gain_with_fail_stack(total, fails))

    return {
        "text": (
            f"🧮 Калькулятор: Кол-во био-опыта\n"
            f"☣️ {_ru_dots(total)} ⇆ 🥽 {_ru_dots(fails)}\n"
            f"💰 Итоговая награда: <b>{_ru_dots(final_gain)}</b>"
        )
    }

def _calc_duel_payload(stacks: int):
    st = max(0, int(stacks or 0))
    aim_bonus = int(st * DUEL_AIM_STEP_PCT)

    base_break = int(DUEL_BREAK_BASE_PCT)
    total_break = int(_duel_break_chance_from_bonus(aim_bonus)) if st > 0 else int(DUEL_BREAK_BASE_PCT)

    lines = [
        "🧮 Калькулятор: ⚔️ Дуэли",
        f"🎯 Стаков: <b>{_ru_dots(st)}</b>",
        f"👁️‍🗨️ Бонус прицеливания: <b>{_fmt_pct_text(float(base_break))} + {_fmt_pct_text(float(aim_bonus))} = {_fmt_pct_text(float(total_break))}</b>",
        f"🪃 Шанс сбить прицел: <b>{_fmt_pct_text(float(total_break))}</b>",
    ]

    return {"text": "\n".join(lines)}

def _inline_plain_target_name(target_id: int) -> str:
    row = get_user_row(int(target_id))
    if not row:
        return "неизвестного пользователя"

    if int(row["is_placeholder"] or 0) == 1:
        un = (row["username"] or "").strip()
        return f"@{un}" if un else "неизвестного пользователя"

    un = (row["username"] or "").strip()
    return display_name(row["first_name"] or "", row["last_name"] or "", un, int(target_id))

def _attempts_phrase_acc(count: int) -> str:
    cnt = int(count)
    if cnt <= 1:
        return "одну попытку"
    return f"{cnt} {_ru_unit(cnt, 'попытку', 'попытки', 'попыток')}"

def _inline_infect_desc(req: dict) -> str:
    if (req.get("kind") or "") == "U":
        tid = int(req["target"])
        cnt = max(1, int(req.get("count") or 1))
        who = _inline_plain_target_name(tid)
        return f"Провести {_attempts_phrase_acc(cnt)} заражения {who}"

    mode = str(req.get("mode") or "r")
    cnt = max(1, int(req.get("count") or 1))
    mode_txt = {
        "r": "случайного объекта",
        "p": "объекта с большим био-опытом",
        "m": "объекта с меньшим био-опытом",
        "e": "объекта с равным био-опытом",
    }.get(mode, "объекта")
    return f"Провести {_attempts_phrase_acc(cnt)} заражения {mode_txt}"

def _inline_calc_req_from_query(query: str):
    raw = (query or "").strip()
    if not raw:
        return None

    toks_raw = raw.split()
    toks = [t.lower() for t in toks_raw]
    if not toks:
        return None

    def _hint(kind: str, title: str, desc: str, text: str, prefix_parts: list[str]):
        return {
            "kind": kind,
            "ready": False,
            "title": title,
            "desc": desc,
            "text": text,
            "reply_markup": _calc_inline_hint_keyboard(_calc_join_prefix(prefix_parts)),
        }

    explicit = False
    mode = "UPG"
    prefix_parts: list[str] = []
    rest_raw = list(toks_raw)
    rest = list(toks)

    if toks[0] in ("к", "калькулятор"):
        explicit = True
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]

        if not rest:
            return _hint(
                "MAIN",
                "Калькулятор",
                "Выберите режим расчёта",
                _calc_inline_error_text("калькулятор", _calc_main_hint_text()),
                prefix_parts
            )

        if rest[0] in CALC_UPGRADE_MODE_ALIASES or rest[0] in ("ку", "кпк"):
            mode = "UPG"
            prefix_parts.append(rest_raw[0])
            rest_raw = rest_raw[1:]
            rest = rest[1:]
        elif rest[0] in CALC_CHANCE_MODE_ALIASES or rest[0] in ("кш", "кпц"):
            mode = "CHANCE"
            prefix_parts.append(rest_raw[0])
            rest_raw = rest_raw[1:]
            rest = rest[1:]
        elif rest[0] in CALC_BUFF_MODE_ALIASES or rest[0] in ("кс", "кус"):
            mode = "BUFF"
            prefix_parts.append(rest_raw[0])
            rest_raw = rest_raw[1:]
            rest = rest[1:]
        elif rest[0] in CALC_EXP_MODE_ALIASES or rest[0] in ("ко"):
            mode = "EXP"
            prefix_parts.append(rest_raw[0])
            rest_raw = rest_raw[1:]
            rest = rest[1:]
        elif rest[0] in CALC_DUEL_MODE_ALIASES or rest[0] in ("кдл"):
            mode = "DUEL"
            prefix_parts.append(rest_raw[0])
            rest_raw = rest_raw[1:]
            rest = rest[1:]
        else:
            return _hint(
                "MAIN",
                "Калькулятор",
                "Выберите режим расчёта",
                _calc_inline_error_text("калькулятор", _calc_main_hint_text()),
                prefix_parts
            )

    elif toks[0] in CALC_UPGRADE_MODE_ALIASES or toks[0] in ("ку", "кпк"):
        explicit = True
        mode = "UPG"
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]
    elif toks[0] in CALC_CHANCE_MODE_ALIASES or toks[0] in ("кш", "кпц"):
        explicit = True
        mode = "CHANCE"
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]
    elif toks[0] in CALC_BUFF_MODE_ALIASES or toks[0] in ("кс", "кус"):
        explicit = True
        mode = "BUFF"
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]
    elif toks[0] in CALC_EXP_MODE_ALIASES or toks[0] in ("ко"):
        explicit = True
        mode = "EXP"
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]
    elif toks[0] in CALC_DUEL_MODE_ALIASES or toks[0] in ("кдл"):
        explicit = True
        mode = "DUEL"
        prefix_parts = [toks_raw[0]]
        rest_raw = toks_raw[1:]
        rest = toks[1:]

    if mode == "EXP":
        if not explicit:
            return None

        if not rest:
            return _hint(
                "EXP",
                "Калькулятор био-опыта",
                "Введите био-опыт и число неудач",
                _calc_inline_error_text("опыт", _calc_exp_hint_text()),
                prefix_parts
            )

        ok_prefix = list(prefix_parts)

        if len(rest) < 2:
            if len(rest) >= 1 and rest[0].isdigit():
                ok_prefix.append(rest_raw[0])
            return _hint(
                "EXP",
                "Калькулятор био-опыта",
                "Введите био-опыт и число неудач",
                _calc_inline_error_text("опыт", _calc_exp_levels_hint_text()),
                ok_prefix
            )

        if not rest[0].isdigit() or not rest[1].isdigit():
            if len(rest) >= 1 and rest[0].isdigit():
                ok_prefix.append(rest_raw[0])
            return _hint(
                "EXP",
                "Калькулятор био-опыта",
                "Введите био-опыт и число неудач",
                _calc_inline_error_text("опыт", _calc_exp_levels_hint_text()),
                ok_prefix
            )

        payload = _calc_exp_payload(int(rest[0]), int(rest[1]))
        return {
            "kind": "EXP",
            "ready": True,
            "title": "Калькулятор био-опыта",
            "desc": "Расчёты выполнены",
            "text": payload["text"],
            "reply_markup": None,
        }

    if mode == "DUEL":
        if not explicit:
            return None

        if not rest:
            return _hint(
                "DUEL",
                "Калькулятор дуэлей",
                "Введите число стаков",
                _calc_inline_error_text("дуэли", _calc_duel_hint_text()),
                prefix_parts
            )

        if not rest[0].isdigit():
            return _hint(
                "DUEL",
                "Калькулятор дуэлей",
                "Введите число стаков",
                _calc_inline_error_text("дуэли", _calc_duel_levels_hint_text()),
                prefix_parts
            )

        payload = _calc_duel_payload(int(rest[0]))
        return {
            "kind": "DUEL",
            "ready": True,
            "title": "Калькулятор дуэлей",
            "desc": "Расчёты выполнены",
            "text": payload["text"],
            "reply_markup": None,
        }

    if mode == "BUFF":
        if not explicit:
            return None

        if not rest:
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_hint_text()),
                prefix_parts
            )

        metric_key = CALC_BUFF_METRIC_ALIASES.get(rest[0])
        if not metric_key:
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_hint_text()),
                prefix_parts
            )

        ok_prefix = prefix_parts + [rest_raw[0]]

        if len(rest) < 3:
            if len(rest) >= 2 and rest[1].isdigit():
                ok_prefix.append(rest_raw[1])
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_levels_hint_text()),
                ok_prefix
            )

        if not rest[1].isdigit() or not rest[2].isdigit():
            if len(rest) >= 2 and rest[1].isdigit():
                ok_prefix.append(rest_raw[1])
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_levels_hint_text()),
                ok_prefix
            )

        n1 = int(rest[1])
        n2 = int(rest[2])
        if n1 >= n2:
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_levels_hint_text()),
                ok_prefix + [rest_raw[1], rest_raw[2]]
            )

        payload = _calc_buff_payload(rest[0], n1, n2)
        if not payload:
            return _hint(
                "BUFF",
                "Калькулятор усилений",
                "Введите показатель и уровни",
                _calc_inline_error_text("усиления", _calc_buff_levels_hint_text()),
                ok_prefix + [rest_raw[1], rest_raw[2]]
            )

        return {
            "kind": "BUFF",
            "ready": True,
            "title": "Калькулятор усилений",
            "desc": "Расчёты выполнены",
            "text": payload["text"],
            "reply_markup": None,
        }

    if mode == "UPG":
        if not explicit:
            if len(rest) != 3:
                return None

            code = _resolve_skill(rest[0])
            if not code or not rest[1].isdigit() or not rest[2].isdigit():
                return None

            n1 = int(rest[1])
            n2 = int(rest[2])
            if n1 >= n2:
                return None

            cost = _calc_cost_range(SKILL_N1[code], n1, n2)
            skill = SKILLS[code]
            return {
                "kind": "UPG",
                "ready": True,
                "title": "Калькулятор улучшения",
                "desc": "Расчёты выполнены",
                "text": (
                    f"🧮 Калькулятор: {skill['emoji']} {h(skill['title_1'])} <b>{n1}</b> → <b>{n2}</b>\n"
                    f"Стоимость 🧬 <b>{_ru_dots(cost)}</b> ({_fmt_k(cost)})"
                ),
                "reply_markup": None,
            }

        if not rest:
            return _hint(
                "UPG",
                "Калькулятор улучшения",
                "Введите название навыка и уровни",
                _calc_inline_error_text("улучшения", _calc_upgrade_hint_text()),
                prefix_parts
            )

        code = _resolve_skill(rest[0])
        if not code:
            return _hint(
                "UPG",
                "Калькулятор улучшения",
                "Введите название навыка и уровни",
                _calc_inline_error_text("улучшения", _calc_upgrade_hint_text()),
                prefix_parts
            )

        ok_prefix = prefix_parts + [rest_raw[0]]

        if len(rest) < 3:
            if len(rest) >= 2 and rest[1].isdigit():
                ok_prefix.append(rest_raw[1])
            return _hint(
                "UPG",
                "Калькулятор улучшения",
                "Введите название навыка и уровни",
                _calc_inline_error_text("улучшения", _calc_upgrade_levels_hint_text()),
                ok_prefix
            )

        if not rest[1].isdigit() or not rest[2].isdigit():
            if len(rest) >= 2 and rest[1].isdigit():
                ok_prefix.append(rest_raw[1])
            return _hint(
                "UPG",
                "Калькулятор улучшения",
                "Введите название навыка и уровни",
                _calc_inline_error_text("улучшения", _calc_upgrade_levels_hint_text()),
                ok_prefix
            )

        n1 = int(rest[1])
        n2 = int(rest[2])
        if n1 >= n2:
            return _hint(
                "UPG",
                "Калькулятор улучшения",
                "Введите название навыка и уровни",
                _calc_inline_error_text("улучшения", _calc_upgrade_levels_hint_text()),
                ok_prefix + [rest_raw[1], rest_raw[2]]
            )

        cost = _calc_cost_range(SKILL_N1[code], n1, n2)
        skill = SKILLS[code]
        return {
            "kind": "UPG",
            "ready": True,
            "title": "Калькулятор улучшения",
            "desc": "Расчёты выполнены",
            "text": (
                f"🧮 Калькулятор: {skill['emoji']} {h(skill['title_1'])} <b>{n1}</b> → <b>{n2}</b>\n"
                f"Стоимость 🧬 <b>{_ru_dots(cost)}</b> ({_fmt_k(cost)})"
            ),
            "reply_markup": None,
        }

    if not explicit:
        return None

    if not rest:
        return _hint(
            "CHANCE",
            "Калькулятор шансов",
            "Введите интересующий параметр",
            _calc_inline_error_text("шансы", _calc_chance_hint_text()),
            prefix_parts
        )

    metric_key = CALC_CHANCE_METRIC_ALIASES.get(rest[0])
    if not metric_key:
        return _hint(
            "CHANCE",
            "Калькулятор шансов",
            "Введите интересующий параметр",
            _calc_inline_error_text("шансы", _calc_chance_hint_text()),
            prefix_parts
        )

    ok_prefix = prefix_parts + [rest_raw[0]]
    metric_prompt = _calc_chance_metric_prompt_text(metric_key)

    if len(rest) < 3:
        if len(rest) >= 2 and rest[1].isdigit():
            ok_prefix.append(rest_raw[1])
        return _hint(
            "CHANCE",
            "Калькулятор шансов",
            "Введите интересующий параметр",
            _calc_inline_error_text("шансы", metric_prompt),
            ok_prefix
        )

    if not rest[1].isdigit() or not rest[2].isdigit():
        if len(rest) >= 2 and rest[1].isdigit():
            ok_prefix.append(rest_raw[1])
        return _hint(
            "CHANCE",
            "Калькулятор шансов",
            "Введите интересующий параметр",
            _calc_inline_error_text("шансы", metric_prompt),
            ok_prefix
        )

    payload = _calc_chance_payload(rest[0], int(rest[1]), int(rest[2]))
    if not payload:
        return _hint(
            "CHANCE",
            "Калькулятор шансов",
            "Введите интересующий параметр",
            _calc_inline_error_text("шансы", metric_prompt),
            ok_prefix + [rest_raw[1], rest_raw[2]]
        )

    return {
        "kind": "CHANCE",
        "ready": True,
        "title": "Калькулятор шансов",
        "desc": "Расчёты выполнены",
        "text": payload["text"],
        "reply_markup": None,
    }

def handle_calc_command(message, parsed: Parsed):
    if not has_explicit_bot_prefix(getattr(message, "text", "") or ""):
        return

    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    def _emit(text: str):
        sent = _REAL_BOT_REPLY_TO(
            message,
            premiumize_html_text(text),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        remember_reply_pair_for_autodelete(sent, message)

    def _emit_err(hint_text: str):
        _emit(_calc_inline_error_text("calc", hint_text))

    parts = (parsed.args or "").strip().split()

    mode = "UPG"
    explicit = False

    if parsed.cmd == "calc_upg":
        mode = "UPG"
        explicit = True
    elif parsed.cmd == "calc_chance":
        mode = "CHANCE"
        explicit = True
    elif parsed.cmd == "calc_buff":
        mode = "BUFF"
        explicit = True
    elif parsed.cmd == "calc_exp":
        mode = "EXP"
        explicit = True
    elif parsed.cmd == "calc_duel":
        mode = "DUEL"
        explicit = True
    else:
        if not parts:
            _emit_err(_calc_main_hint_text())
            return

        first = parts[0].lower()
        if first in CALC_UPGRADE_MODE_ALIASES:
            mode = "UPG"
            explicit = True
            parts = parts[1:]
        elif first in CALC_CHANCE_MODE_ALIASES:
            mode = "CHANCE"
            explicit = True
            parts = parts[1:]
        elif first in CALC_BUFF_MODE_ALIASES:
            mode = "BUFF"
            explicit = True
            parts = parts[1:]
        elif first in CALC_EXP_MODE_ALIASES:
            mode = "EXP"
            explicit = True
            parts = parts[1:]
        elif first in CALC_DUEL_MODE_ALIASES:
            mode = "DUEL"
            explicit = True
            parts = parts[1:]
        else:
            mode = "UPG"
            explicit = False

    if mode == "BUFF":
        if not parts:
            _emit_err(_calc_buff_hint_text())
            return

        metric_key = CALC_BUFF_METRIC_ALIASES.get(parts[0].lower())
        if not metric_key:
            _emit_err(_calc_buff_hint_text())
            return

        if len(parts) < 3:
            _emit_err(_calc_buff_levels_hint_text())
            return

        try:
            n1 = int(parts[1])
            n2 = int(parts[2])
        except Exception:
            _emit_err(_calc_buff_levels_hint_text())
            return

        if n1 >= n2:
            _emit_err(_calc_buff_levels_hint_text())
            return

        payload = _calc_buff_payload(parts[0], n1, n2)
        if not payload:
            _emit_err(_calc_buff_levels_hint_text())
            return

        _emit(payload["text"])
        return

    if mode == "EXP":
        if not parts:
            _emit_err(_calc_exp_levels_hint_text())
            return

        if len(parts) < 2:
            _emit_err(_calc_exp_levels_hint_text())
            return

        try:
            total = int(parts[0])
            fails = int(parts[1])
        except Exception:
            _emit_err(_calc_exp_levels_hint_text())
            return

        if total < 0 or fails < 0:
            _emit_err(_calc_exp_levels_hint_text())
            return

        payload = _calc_exp_payload(total, fails)
        _emit(payload["text"])
        return

    if mode == "DUEL":
        if not parts:
            _emit_err(_calc_duel_levels_hint_text())
            return

        try:
            stacks = int(parts[0])
        except Exception:
            _emit_err(_calc_duel_levels_hint_text())
            return

        if stacks < 0:
            _emit_err(_calc_duel_levels_hint_text())
            return

        payload = _calc_duel_payload(stacks)
        _emit(payload["text"])
        return

    if mode == "UPG":
        if not parts:
            if explicit:
                _emit_err(_calc_upgrade_hint_text())
            else:
                _emit_err(_calc_main_hint_text())
            return

        code = _resolve_skill(parts[0])
        if not code or code not in SKILLS:
            if explicit:
                _emit_err(_calc_upgrade_hint_text())
            else:
                _emit_err(_calc_upgrade_hint_text())
            return

        if len(parts) < 3:
            _emit_err(_calc_upgrade_levels_hint_text())
            return

        try:
            n1 = int(parts[1])
            n2 = int(parts[2])
        except Exception:
            _emit_err(_calc_upgrade_levels_hint_text())
            return

        if n1 >= n2:
            _emit_err(_calc_upgrade_levels_hint_text())
            return

        cost = _calc_cost_range(SKILL_N1[code], n1, n2)
        skill = SKILLS[code]

        _emit(
            f"🧮 Калькулятор: {skill['emoji']} {h(skill['title_1'])} <b>{n1}</b> → <b>{n2}</b>\n"
            f"Стоимость 🧬 <b>{_ru_dots(cost)}</b> ({_fmt_k(cost)})"
        )
        return

    if not parts:
        _emit_err(_calc_chance_hint_text())
        return

    metric_key = CALC_CHANCE_METRIC_ALIASES.get(parts[0].lower())
    if not metric_key:
        _emit_err(_calc_chance_hint_text())
        return

    if len(parts) < 3:
        _emit_err(_calc_chance_metric_prompt_text(metric_key))
        return

    try:
        n1 = int(parts[1])
        n2 = int(parts[2])
    except Exception:
        _emit_err(_calc_chance_metric_prompt_text(metric_key))
        return

    payload = _calc_chance_payload(parts[0], n1, n2)
    if not payload:
        _emit_err(_calc_chance_metric_prompt_text(metric_key))
        return

    _emit(payload["text"])

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{UPGUI_TAG}:"))
def cb_upgrade(cq):
    try:
        info = _upg_cb_parse(cq.data or "")
        if not info:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(info["uid"]):
            bot.answer_callback_query(cq.id)
            return

        uid = int(info["uid"])
        code = info["code"]
        steps = int(info["steps"])
        action = info["action"]
        src = info.get("src", "C")
        ictype = info.get("ictype")
        ictx = info.get("ictx") or []

        if code not in SKILLS:
            bot.answer_callback_query(cq.id)
            return

        inline_id = cq.inline_message_id if getattr(cq, "inline_message_id", None) else None
        has_normal_message = bool(getattr(cq, "message", None))

        if not inline_id and not has_normal_message:
            bot.answer_callback_query(cq.id)
            return

        def _edit(text: str, reply_markup=None):
            if inline_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=inline_id,
                    parse_mode="HTML",
                    reply_markup=reply_markup,
                    disable_web_page_preview=True
                )
                return

            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=True
            )

        if action == "SP":
            ok, txt, _ = _execute_upgrade_by_skill_point(uid, code)

            st = get_balance_chain_state(int(uid))
            state_code = ""
            state_steps = int(steps)
            state_src = src
            state_ictype = ictype
            state_ictx = ictx or []

            if st and str(st.get("chain_kind") or "") == BALCHAIN_UPGRADE:
                payload = (st.get("payload") or {})
                state_code, state_steps, state_src, state_ictype, state_ictx = _upgrade_payload_parts(payload)

            if ok:
                if state_code == code:
                    rm = kb_upgrade_shortage(uid, code, state_steps, state_src, ictype=state_ictype, ictx=state_ictx, include_balance=True)
                    rm = _append_upgrade_return_buttons(rm, uid, state_src, state_ictype, state_ictx)
                else:
                    rm = kb_upgrade(uid, code, 1, src, ictype=ictype, ictx=ictx)
                    rm = _append_upgrade_return_buttons(rm, uid, src, ictype, ictx)
            else:
                rm = None

            _edit(txt, reply_markup=rm)
            bot.answer_callback_query(cq.id)
            return

        if action == "P":
            txt = _build_upgrade_preview(uid, code, steps)
            rm = kb_upgrade(uid, code, steps, src, ictype=ictype, ictx=ictx)
            if src == "D":
                rm.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D"), style="primary"))
            elif src == "PB":
                rm.row(InlineKeyboardButton("Вернуться к сводке", callback_data=_pathogens_ui_data(uid, "INFO", 0), style="primary"))
            _edit(txt, reply_markup=rm)
            bot.answer_callback_query(cq.id)
            return

        ok, txt, _ = _execute_upgrade(uid, code, steps)

        rm = None
        if ok:
            st = get_balance_chain_state(int(uid))
            if st and str(st.get("chain_kind") or "") == BALCHAIN_UPGRADE:
                clear_balance_chain_state(int(uid))

            rm = kb_upgrade(uid, code, steps, src, ictype=ictype, ictx=ictx)

            if src == "D":
                rm.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D"), style="primary"))
            elif src == "PB":
                rm.row(InlineKeyboardButton("Вернуться к сводке", callback_data=_pathogens_ui_data(uid, "INFO", 0), style="primary"))

            if src == "I" and ictype:
                try:
                    if ictype == "U" and len(ictx) >= 1:
                        t_id = int(ictx[0])
                        rm.row(
                            InlineKeyboardButton("Попробовать ещё раз", callback_data=f"{INFUI_TAG}:U:{uid}:{t_id}:1"),
                        )
                        rm.row(
                            InlineKeyboardButton("× 2", callback_data=f"{INFUI_TAG}:U:{uid}:{t_id}:2"),
                            InlineKeyboardButton("× 5", callback_data=f"{INFUI_TAG}:U:{uid}:{t_id}:5"),
                            InlineKeyboardButton("× 10", callback_data=f"{INFUI_TAG}:U:{uid}:{t_id}:10"),
                        )
                    elif ictype == "M" and len(ictx) >= 2:
                        mode = str(ictx[0])
                        flt = str(ictx[1])
                        rm.row(
                            InlineKeyboardButton("Попробовать ещё раз", callback_data=f"{INFUI_TAG}:M:{uid}:{mode}:{flt}:1"),
                        )
                        rm.row(
                            InlineKeyboardButton("× 2", callback_data=f"{INFUI_TAG}:M:{uid}:{mode}:{flt}:2"),
                            InlineKeyboardButton("× 5", callback_data=f"{INFUI_TAG}:M:{uid}:{mode}:{flt}:5"),
                            InlineKeyboardButton("× 10", callback_data=f"{INFUI_TAG}:M:{uid}:{mode}:{flt}:10"),
                        )
                except Exception:
                    pass
        else:
            source_chat_id = int(getattr(getattr(cq, "message", None), "chat", None).id) if getattr(cq, "message", None) and getattr(cq.message, "chat", None) else 0
            source_message_id = int(getattr(getattr(cq, "message", None), "message_id", 0) or 0)

            set_balance_chain_state(
                int(uid),
                BALCHAIN_UPGRADE,
                _balance_chain_upgrade_button_text(code, steps),
                _upgrade_balance_payload(code, steps, src, ictype, ictx),
                source_chat_id=source_chat_id,
                source_message_id=source_message_id
            )

            txt = _upgrade_shortage_text(int(uid))
            rm = kb_upgrade_shortage(uid, code, steps, src, ictype=ictype, ictx=ictx, include_balance=True) if _upgrade_skill_points_count(int(uid)) > 0 else kb_open_balance(int(uid))
            rm = _append_upgrade_return_buttons(rm, uid, src, ictype, ictx)

        _edit(txt, reply_markup=rm)
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_upgrade", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

#           баланс и синтез
def handle_balance_command(message, parsed: Optional[Parsed] = None):
    viewer_id = int(message.from_user.id)

    target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)

    tok = (parsed.args.split()[0] if (parsed and parsed.args) else "")
    if is_bot_target(target_id, target_user_obj, tok):
        bot.reply_to(message, bot_cannot_have("личного счёта"))
        return

    if target_id is None:
        target_id = viewer_id
        target_user_obj = message.from_user

    if target_user_obj is not None:
        capture_user_context(message, target_user_obj)

    ensure_lab_exists(target_id)

    if int(target_id) == int(viewer_id):
        hb, _hl = get_privacy_flags(int(viewer_id))
        rm = kb_balance_self(viewer_id)
        text = render_balance(target_id)

        if message.chat.type in ("group", "supergroup") and hb == 1:
            sent = _send_hidden_self_info_to_pm(int(viewer_id), text, reply_markup=rm)
            if sent:
                bot.reply_to(
                    message,
                    "📋 Информация о вашем балансе отправлена в личные сообщения.",
                    reply_markup=kb_open_bot_pm()
                )
            else:
                bot.reply_to(
                    message,
                    "📑 Не удалось отправить информацию в личные сообщения. Сначала откройте личный чат с ботом.",
                    reply_markup=kb_open_bot_pm()
                )
            return

        bot.reply_to(message, text, disable_web_page_preview=True, reply_markup=rm)
        return

    hb, _hl = get_privacy_flags(int(target_id))
    if hb == 1 and not same_corp(int(viewer_id), int(target_id)):
        bot.reply_to(message, "🔒 Баланс скрыт пользователем.")
        return
    bot.reply_to(message, render_balance(target_id), disable_web_page_preview=True)

def render_balance(user_id: int) -> str:
    ensure_lab_exists(user_id)

    row = db_one(
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m, COALESCE(skill_points,0) AS sp FROM labs WHERE user_id=?",
        (int(user_id),),
    )
    all_bio_res = int(row["r"] if row else 0)
    all_bio_mater = int(row["m"] if row else 0)
    skill_points = int(row["sp"] if row else 0)

    u = get_user_row(user_id)
    un = (u["username"] or "") if u else ""
    disp = display_name(
        (u["first_name"] or "") if u else "",
        (u["last_name"] or "") if u else "",
        un,
        int(user_id),
    )
    who = tg_mention(int(user_id), disp, username=un)

    res_word = _ru_form(all_bio_res, "био-ресурс", "био-ресурса", "био-ресурсов")
    mat_word = _ru_form(all_bio_mater, "био-материал", "био-материала", "био-материалов")

    pts_line = ""
    if skill_points > 0:
        pts_word = _ru_form(skill_points, "очко навыка", "очка навыка", "очков навыка")
        pts_line = f"🔹 {_fmt_k(skill_points)} {pts_word}\n"

    return (
        f"Баланс <b>{who}</b>:\n"
        f"🧬 {_fmt_k(all_bio_res)} {res_word}\n"
        f"💊 {_fmt_k(all_bio_mater)} {mat_word}\n"
        f"{pts_line}"
        f"💬 Запасы можно пополнить командой \"<code>Синтез</code>\""
    )

def _balui_data(uid: int, act: str, extra: str = "") -> str:
    base = f"{BALUI_TAG}:{int(uid)}:{act}"
    extra = str(extra or "").strip()
    if not extra:
        return base
    return f"{base}:{extra}"

def _balui_parse(data: str):
    try:
        p = (data or "").split(":")
        if len(p) < 3 or p[0] != BALUI_TAG:
            return None, None, ""
        uid = int(p[1])
        act = str(p[2] or "").strip()
        extra = ":".join(p[3:]).strip() if len(p) > 3 else ""
        return uid, act, extra
    except Exception:
        return None, None, ""

def synth_left_seconds(uid: int) -> int:
    ensure_lab_exists(uid)
    row = db_one("SELECT COALESCE(last_synth_ts,0) AS t FROM labs WHERE user_id=?", (int(uid),))
    last_ts = int(row["t"] if row else 0)
    left = (last_ts + SYNTH_COOLDOWN_SEC) - now_ts()
    return int(left) if left > 0 else 0

def kb_balance_self(uid: int) -> Optional[InlineKeyboardMarkup]:
    kb = InlineKeyboardMarkup()

    state = get_balance_chain_state(int(uid))
    can_resume = False
    btn_text = ""
    if state:
        can_resume, btn_text = _balance_chain_can_resume(int(uid), state)

    if can_resume and btn_text:
        chain_kind = str((state or {}).get("chain_kind") or "").strip()
        if chain_kind == BALCHAIN_UPGRADE:
            payload = (state or {}).get("payload") or {}
            code, steps, _src, _ictype, _ictx = _upgrade_payload_parts(payload)
            kb.add(
                _balance_chain_upgrade_button(
                    code,
                    steps,
                    callback_data=_balui_data(int(uid), "R"),
                    style="primary"
                )
            )
        else:
            kb.add(InlineKeyboardButton(btn_text, callback_data=_balui_data(int(uid), "R"), style="primary"))

    if synth_left_seconds(uid) <= 0:
        kb.add(_ikb_premium_counter("⚗️", "Синтез", callback_data=_balui_data(uid, "S")))

    kb = _append_balance_return_buttons(kb, int(uid))

    return kb if getattr(kb, "keyboard", None) else None

def kb_balance_after_synth(uid: int) -> Optional[InlineKeyboardMarkup]:
    state = get_balance_chain_state(int(uid))
    if state and str(state.get("chain_kind") or "") == BALCHAIN_UPGRADE:
        return _kb_balance_upgrade_actions(int(uid), state, from_synth=True)

    kb = InlineKeyboardMarkup()

    btn_text = str((state or {}).get("button_text") or "").strip()
    if btn_text:
        kb.add(InlineKeyboardButton(btn_text, callback_data=_balui_data(int(uid), "R", "S"), style="primary"))

    if synth_left_seconds(uid) <= 0:
        kb.add(_ikb_premium_counter("⚗️", "Синтез", callback_data=_balui_data(uid, "S")))
    
    kb = _append_balance_return_buttons(kb, int(uid))

    return kb if getattr(kb, "keyboard", None) else None

def kb_open_balance(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Баланс", callback_data=_balui_data(int(uid), "B"), style="primary"))
    return kb

def _balance_chain_upgrade_button_parts(code: str, steps: int) -> tuple[str, str]:
    skill = SKILLS.get(str(code or "").strip().upper())
    emo = str(skill["emoji"] if skill else "").strip()
    steps = max(1, int(steps or 1))

    if steps <= 1:
        return emo, "Повторить улучшение"

    return emo, f"Повторить × {steps}"

def _balance_chain_upgrade_button_text(code: str, steps: int) -> str:
    emo, label = _balance_chain_upgrade_button_parts(code, steps)
    return f"{label} {emo}".strip()

def _balance_chain_upgrade_button(
    code: str,
    steps: int,
    *,
    callback_data: str,
    style: str = "primary"
):
    emo, label = _balance_chain_upgrade_button_parts(code, steps)
    return _ikb_premium_lead(
        emo,
        label,
        callback_data=callback_data,
        style=style
    )

def _balance_chain_can_resume(uid: int, state: dict) -> tuple[bool, str]:
    if not state:
        return False, ""

    kind = str(state.get("chain_kind") or "").strip()
    payload = state.get("payload") or {}
    if not isinstance(payload, dict):
        payload = {}

    ensure_lab_exists(int(uid))
    row = db_one(
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m, COALESCE(skill_points,0) AS sp "
        "FROM labs WHERE user_id=?",
        (int(uid),)
    )
    have_r = int(row["r"] or 0) if row else 0
    have_m = int(row["m"] or 0) if row else 0

    if kind == BALCHAIN_UPGRADE:
        code = str(payload.get("code") or "").strip().upper()
        steps = max(1, int(payload.get("steps") or 1))
        if code not in SKILLS:
            return False, ""

        lab = get_lab(int(uid))
        cur = int(_rget(lab, SKILLS[code]["col"], 1) or 1)
        cost = _upgrade_cost(SKILL_N1[code], cur, steps)
        if (have_r + have_m) >= int(cost):
            return True, _balance_chain_upgrade_button_text(code, steps)
        return False, ""

    if kind == BALCHAIN_CORP_TRANSFER:
        cmd = str(payload.get("cmd") or "").strip()
        amount = max(1, int(payload.get("amount") or 0))
        plan = _corp_transfer_plan(int(uid), cmd, int(amount))
        if bool(plan.get("ok")):
            return True, "Повторить перевод"
        return False, ""

    if kind == BALCHAIN_VACCINE:
        fever_until, _fever_pat, vac_cnt = get_fever_and_vaccines(int(uid))
        now = now_ts()
        if fever_until <= now:
            return False, ""

        if int(vac_cnt) > 0:
            return True, "Использовать вакцину"

        need = int(get_vaccine_price(int(uid)))
        if (have_r + have_m) >= need:
            return True, "Повторить покупку"
        return False, ""

    if kind == BALCHAIN_DUEL_BET:
        amount = max(1, int(payload.get("amount") or 0))
        if have_m >= amount:
            return True, "Повторить ставку"
        return False, ""

    if kind == BALCHAIN_DUEL_STAKE:
        stake_amount = max(1, int(payload.get("stake_amount") or 0))
        if have_m >= stake_amount:
            return True, "Повторить вызов"
        return False, ""

    return False, ""

def _balance_chain_fake_message(cq, uid: int, state: dict):
    class _FakeChat:
        pass

    class _FakeMsg:
        pass

    fm = _FakeMsg()
    fm.from_user = cq.from_user
    fm.reply_to_message = None
    fm.text = ""
    fm.via_bot = None
    fm.content_type = "text"
    fm.date = now_ts()

    fc = _FakeChat()
    if getattr(cq, "message", None) and getattr(cq.message, "chat", None):
        fc.id = int(cq.message.chat.id)
        fc.type = (getattr(cq.message.chat, "type", None) or ("private" if int(fc.id) > 0 else "group"))
        fm.message_id = int(getattr(cq.message, "message_id", 0) or 0)
    else:
        src_chat_id = int(state.get("source_chat_id") or 0)
        if src_chat_id == 0:
            src_chat_id = int(uid)
        fc.id = int(src_chat_id)
        fc.type = "private" if int(src_chat_id) > 0 else "group"
        fm.message_id = int(state.get("source_message_id") or 0)

    fm.chat = fc
    return fm

def _balance_chain_edit_ctx_from_cq(cq, state: dict) -> Optional[dict]:
    if getattr(cq, "inline_message_id", None):
        return {"inline_id": str(cq.inline_message_id)}

    if getattr(cq, "message", None) and getattr(cq.message, "chat", None):
        chat_id = int(getattr(cq.message.chat, "id", 0) or 0)
        msg_id = int(getattr(cq.message, "message_id", 0) or 0)
        if chat_id != 0 and msg_id != 0:
            return {"chat_id": chat_id, "msg_id": msg_id}

    src_chat_id = int(state.get("source_chat_id") or 0)
    src_msg_id = int(state.get("source_message_id") or 0)
    if src_chat_id != 0 and src_msg_id != 0:
        return {"chat_id": src_chat_id, "msg_id": src_msg_id}

    return None

def _balance_chain_emit(message, text: str, reply_markup=None, edit_ctx: Optional[dict] = None):
    if edit_ctx and isinstance(edit_ctx, dict):
        inline_id = edit_ctx.get("inline_id")
        chat_id = edit_ctx.get("chat_id")
        msg_id = edit_ctx.get("msg_id")

        if inline_id:
            limited_edit_message_text(
                text=text,
                inline_id=inline_id,
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=True
            )
            return

        if chat_id and msg_id:
            limited_edit_message_text(
                text=text,
                chat_id=int(chat_id),
                msg_id=int(msg_id),
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=True
            )
            return

    bot.reply_to(
        message,
        text,
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=reply_markup
    )

def _resume_vaccine_chain_from_balance(message, uid: int, edit_ctx: Optional[dict] = None):
    fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(int(uid))
    now = now_ts()

    if fever_until <= now:
        clear_balance_chain_state(int(uid))
        _balance_chain_emit(
            message,
            "📝 У вас нет горячки. Нет необходимости покупать или использовать вакцину.",
            reply_markup=None,
            edit_ctx=edit_ctx
        )
        return

    if int(vac_cnt) > 0:
        status, used = try_use_vaccine(int(uid), 1)
        if status == "OK":
            clear_balance_chain_state(int(uid))
            _balance_chain_emit(
                message,
                "💉 Вакцина излечила вас от горячки.\n🧾 Потрачена 1 единица вакцины",
                reply_markup=None,
                edit_ctx=edit_ctx
            )
            return
        if status == "FAIL":
            _balance_chain_emit(
                message,
                VACCINE_FAIL_TEXT,
                reply_markup=kb_vaccine_retry(int(uid)),
                edit_ctx=edit_ctx
            )
            return
        if status == "NO_VACCINE":
            set_balance_chain_state_from_message(
                message,
                BALCHAIN_VACCINE,
                "Повторить покупку",
                {"action": "buy"}
            )
            _balance_chain_emit(
                message,
                "📝 У вас нет вакцины.",
                reply_markup=kb_open_balance(int(uid)),
                edit_ctx=edit_ctx
            )
            return

        clear_balance_chain_state(int(uid))
        _balance_chain_emit(
            message,
            "📝 У вас нет горячки. Нет необходимости использовать вакцину.",
            reply_markup=None,
            edit_ctx=edit_ctx
        )
        return

    status, spent_res, spent_mat = try_buy_vaccine(int(uid))
    if status == "NO_MONEY":
        set_balance_chain_state_from_message(
            message,
            BALCHAIN_VACCINE,
            "Повторить покупку",
            {"action": "buy"}
        )
        _balance_chain_emit(
            message,
            "📝 У вас недостаточно средств.",
            reply_markup=kb_open_balance(int(uid)),
            edit_ctx=edit_ctx
        )
        return

    if status == "NO_FEVER":
        clear_balance_chain_state(int(uid))
        _balance_chain_emit(
            message,
            "📝 У вас нет горячки. Нет необходимости покупать вакцину.",
            reply_markup=None,
            edit_ctx=edit_ctx
        )
        return

    if status == "FAIL":
        clear_balance_chain_state(int(uid))
        _balance_chain_emit(
            message,
            VACCINE_FAIL_TEXT,
            reply_markup=kb_vaccine_retry(int(uid)),
            edit_ctx=edit_ctx
        )
        return

    clear_balance_chain_state(int(uid))
    _balance_chain_emit(
        message,
        "💉 Вакцина излечила вас от горячки.\n"
        f"🧾 Потрачено {vaccine_spent_text(spent_res, spent_mat)}",
        reply_markup=None,
        edit_ctx=edit_ctx
    )

def _resume_balance_chain(cq, uid: int, *, force_attempt: bool = False):
    state = get_balance_chain_state(int(uid))
    if not state:
        return False

    can_resume, _btn_text = _balance_chain_can_resume(int(uid), state)
    if not can_resume and not force_attempt:
        return False

    kind = str(state.get("chain_kind") or "").strip()
    payload = state.get("payload") or {}
    if not isinstance(payload, dict):
        payload = {}

    fake_msg = _balance_chain_fake_message(cq, int(uid), state)
    edit_ctx = _balance_chain_edit_ctx_from_cq(cq, state)

    if kind == BALCHAIN_UPGRADE:
        code, steps, src, ictype, ictx = _upgrade_payload_parts(payload)
        if code not in SKILLS:
            return False

        ok, txt, _final = _execute_upgrade(int(uid), code, int(steps))
        if ok:
            st = get_balance_chain_state(int(uid))
            if st and str(st.get("chain_kind") or "") == BALCHAIN_UPGRADE:
                clear_balance_chain_state(int(uid))

            rm = kb_upgrade(int(uid), code, int(steps), src, ictype=ictype, ictx=ictx)
            rm = _append_upgrade_return_buttons(rm, int(uid), src, ictype, ictx)
            _balance_chain_emit(fake_msg, txt, reply_markup=rm, edit_ctx=edit_ctx)
            return True

        set_balance_chain_state(
            int(uid),
            BALCHAIN_UPGRADE,
            _balance_chain_upgrade_button_text(code, steps),
            _upgrade_balance_payload(code, steps, src, ictype, ictx),
            source_chat_id=int(getattr(getattr(fake_msg, "chat", None), "id", 0) or 0),
            source_message_id=int(getattr(fake_msg, "message_id", 0) or 0),
        )

        fail_text = _upgrade_shortage_text(int(uid))
        rm = kb_upgrade_shortage(int(uid), code, int(steps), src, ictype=ictype, ictx=ictx, include_balance=True) if _upgrade_skill_points_count(int(uid)) > 0 else kb_open_balance(int(uid))
        rm = _append_upgrade_return_buttons(rm, int(uid), src, ictype, ictx)
        _balance_chain_emit(fake_msg, fail_text, reply_markup=rm, edit_ctx=edit_ctx)
        return True

    if kind == BALCHAIN_CORP_TRANSFER:
        cmd = str(payload.get("cmd") or "").strip()
        amount = max(1, int(payload.get("amount") or 0))
        target_id = int(payload.get("target_id") or 0)
        if cmd not in ("corp_send_res", "corp_send_mat") or target_id <= 0:
            return False

        plan = _corp_transfer_plan(int(uid), cmd, int(amount))
        if not bool(plan.get("ok")):
            set_balance_chain_state_from_message(
                fake_msg,
                BALCHAIN_CORP_TRANSFER,
                "Повторить перевод",
                {"cmd": cmd, "amount": int(amount), "target_id": int(target_id)}
            )
            _balance_chain_emit(
                fake_msg,
                _corp_transfer_shortage_error(cmd),
                reply_markup=kb_open_balance(int(uid)),
                edit_ctx=edit_ctx
            )
            return True

        if bool(plan.get("mixed")) or bool(plan.get("substitute_only")):
            set_balance_chain_state_from_message(
                fake_msg,
                BALCHAIN_CORP_TRANSFER,
                "Повторить перевод",
                {"cmd": cmd, "amount": int(amount), "target_id": int(target_id)}
            )
            _balance_chain_emit(
                fake_msg,
                _corp_transfer_mix_text(cmd, int(target_id), int(plan["res_amount"]), int(plan["mat_amount"])),
                reply_markup=kb_corp_transfer_mix_offer(
                    int(uid),
                    cmd,
                    int(target_id),
                    int(plan["res_amount"]),
                    int(plan["mat_amount"])
                ),
                edit_ctx=edit_ctx
            )
            return True

        try:
            ok, err = _corp_transfer_apply(
                int(uid),
                int(target_id),
                res_amount=int(plan["res_amount"]),
                mat_amount=int(plan["mat_amount"])
            )
        except Exception as e:
            send_error_report("resume_corp_transfer", e)
            _balance_chain_emit(fake_msg, "📑 Не удалось выполнить перевод.", reply_markup=None, edit_ctx=edit_ctx)
            return True

        if not ok:
            if err in ("📝 У вас нет столько био-ресурсов.", "📝 У вас нет столько био-материалов."):
                set_balance_chain_state_from_message(
                    fake_msg,
                    BALCHAIN_CORP_TRANSFER,
                    "Повторить перевод",
                    {"cmd": cmd, "amount": int(amount), "target_id": int(target_id)}
                )
                _balance_chain_emit(fake_msg, err, reply_markup=kb_open_balance(int(uid)), edit_ctx=edit_ctx)
            else:
                _balance_chain_emit(fake_msg, err, reply_markup=None, edit_ctx=edit_ctx)
            return True

        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_CORP_TRANSFER:
            clear_balance_chain_state(int(uid))

        txt = _corp_transfer_success_text(
            int(target_id),
            int(plan["res_amount"]),
            int(plan["mat_amount"])
        )
        _balance_chain_emit(fake_msg, txt, reply_markup=None, edit_ctx=edit_ctx)
        return True

    if kind == BALCHAIN_DUEL_BET:
        amount = max(1, int(payload.get("amount") or 0))
        target_id = int(payload.get("target_id") or 0)
        if target_id <= 0:
            return False

        chat_id = int(getattr(getattr(fake_msg, "chat", None), "id", 0) or 0)

        try:
            ok, msg, duel_row = _duel_place_bet(int(chat_id), int(uid), int(target_id), int(amount))
        except Exception as e:
            send_error_report("resume_duel_bet_place", e)
            _balance_chain_emit(fake_msg, "📑 Не удалось сделать ставку.", reply_markup=None, edit_ctx=edit_ctx)
            return True

        if not ok:
            if msg == "📝 У вас нет столько био-материалов для ставки.":
                set_balance_chain_state_from_message(
                    fake_msg,
                    BALCHAIN_DUEL_BET,
                    "Повторить ставку",
                    {"amount": int(amount), "target_id": int(target_id)}
                )
                _balance_chain_emit(fake_msg, msg, reply_markup=kb_open_balance(int(uid)), edit_ctx=edit_ctx)
            else:
                _balance_chain_emit(fake_msg, msg, reply_markup=None, edit_ctx=edit_ctx)
            return True

        with chat_name_context(int(chat_id)):
            target_tag = public_user_tag(int(target_id))

        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_DUEL_BET:
            clear_balance_chain_state(int(uid))

        _balance_chain_emit(
            fake_msg,
            f"💰 Вы сделали ставку на дуэлянта <b>{target_tag}</b> в размере 💊 {_duel_stake_text(int(amount))}\n"
            "Дождитесь окончания дуэли. Мы сообщим вам, если ваша ставка сыграет.",
            reply_markup=None,
            edit_ctx=edit_ctx
        )
        return True

    if kind == BALCHAIN_DUEL_STAKE:
        stake_amount = max(1, int(payload.get("stake_amount") or 0))
        target_id = int(payload.get("target_id") or 0)
        if target_id <= 0:
            return False

        chat_id = int(getattr(getattr(fake_msg, "chat", None), "id", 0) or 0)

        if _duel_user_has_active_duel_in_chat(int(chat_id), int(uid)) or _duel_user_has_outgoing_pending_invite_in_chat(int(chat_id), int(uid)):
            _balance_chain_emit(fake_msg, "📑 Вы уже участвуете в дуэли или ожидаете ответа на свой вызов в этом чате.", reply_markup=None, edit_ctx=edit_ctx)
            return True

        if _duel_user_has_active_duel_in_chat(int(chat_id), int(target_id)):
            _balance_chain_emit(fake_msg, "📑 Этот пользователь уже участвует в другой дуэли в этом чате.", reply_markup=None, edit_ctx=edit_ctx)
            return True

        if stake_amount > 0 and not _duel_take_materials(int(uid), int(stake_amount)):
            set_balance_chain_state_from_message(
                fake_msg,
                BALCHAIN_DUEL_STAKE,
                "Повторить вызов",
                {"stake_amount": int(stake_amount), "target_id": int(target_id)}
            )
            _balance_chain_emit(
                fake_msg,
                "📝 У вас недостаточно био-материалов для дуэли со ставкой.",
                reply_markup=kb_open_balance(int(uid)),
                edit_ctx=edit_ctx
            )
            return True

        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_DUEL_STAKE:
            clear_balance_chain_state(int(uid))

        invite_id = 0
        try:
            invite_id = _duel_create_invite(int(chat_id), int(uid), int(target_id), int(stake_amount))
            txt = _duel_invite_text(int(chat_id), int(uid), int(target_id), int(stake_amount))
            rm = kb_duel_invite(int(invite_id), int(target_id), int(uid))

            _balance_chain_emit(fake_msg, txt, reply_markup=rm, edit_ctx=edit_ctx)

            if edit_ctx and edit_ctx.get("chat_id") and edit_ctx.get("msg_id"):
                _duel_mark_invite_message(int(invite_id), int(edit_ctx["chat_id"]), int(edit_ctx["msg_id"]))
        except Exception as e:
            if int(stake_amount or 0) > 0:
                _duel_refund_materials(int(uid), int(stake_amount))
            try:
                if int(invite_id or 0) > 0:
                    db_exec("DELETE FROM duel_invites WHERE invite_id=?", (int(invite_id),), commit=True)
            except Exception:
                pass
            send_error_report("resume_duel_create_invite", e)
            _balance_chain_emit(fake_msg, "📑 Не удалось отправить вызов на дуэль.", reply_markup=None, edit_ctx=edit_ctx)
            return True

        return True

    if kind == BALCHAIN_VACCINE:
        _resume_vaccine_chain_from_balance(fake_msg, int(uid), edit_ctx=edit_ctx)
        return True

    return False

def kb_synth(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Баланс", callback_data=_balui_data(uid, "B", "S"), style="primary"))
    return kb

def synth_attempt(uid: int) -> str:
    """Возвращает текст синтеза (успех или кулдаун)."""
    ensure_lab_exists(uid)
    now = now_ts()

    row = db_one(
        "SELECT COALESCE(last_synth_ts,0) AS t, COALESCE(synthesis,1) AS syn "
        "FROM labs WHERE user_id=?",
        (uid,)
    )
    last_ts = int(row["t"] if row else 0)
    synth_lvl = int(row["syn"] if row else 1)

    left = (last_ts + SYNTH_COOLDOWN_SEC) - now
    if left > 0:
        return f"❌ СИНТЕЗ НЕ ВЫПОЛНЕН! Ограничение раз в 4 часа. Следующая добыча через {_format_duration(left)}"

    synth_bonus = _synth_bonus_value(synth_lvl)
    base_min = 1
    base_max = 100 + synth_bonus
    base_value = random.randint(base_min, base_max)
    cof_rost = _pick_cof_rost()
    bio_mater = int((base_value + synth_bonus) * cof_rost)

    db_exec(
        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+?, last_synth_ts=? WHERE user_id=?",
        (bio_mater, now, uid),
        commit=True
    )

    return (
        f"⚗️ СИНТЕЗ ЗАВЕРШЁН! Получено 💊 +{bio_mater} = ( {base_value} + {synth_bonus} ) × {cof_rost}\n\n"
        f"🔺 Коэффициент роста: {cof_rost}\n"
        f"📈 Эффективность синтеза: +{synth_bonus}"
    )

def handle_synth_command(message):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    text = synth_attempt(uid)
    bot.reply_to(message, text, reply_markup=kb_synth(uid), disable_web_page_preview=True)

#             краткая сводка
def _normalize_quick_infect_pref(mode: str, chat_filter: str = "n") -> tuple[str, str]:
    m = str(mode or "r").strip().lower()
    f = str(chat_filter or "n").strip().lower()

    if m not in ("r", "p", "m", "e", "c"):
        m = "r"

    if m != "c":
        f = "n"
    elif f not in ("n", "p", "m", "e"):
        f = "n"

    return m, f

def _quick_infect_pref_row(user_id: int):
    return db_one(
        "SELECT user_id, mode, chat_filter, updated_at "
        "FROM quick_infect_prefs WHERE user_id=? LIMIT 1",
        (int(user_id),)
    )

def get_quick_infect_pref(user_id: int) -> tuple[str, str]:
    row = _quick_infect_pref_row(int(user_id))
    if not row:
        return "r", "n"
    return _normalize_quick_infect_pref(row["mode"], row["chat_filter"])

def set_quick_infect_pref(user_id: int, mode: str, chat_filter: str = "n"):
    m, f = _normalize_quick_infect_pref(mode, chat_filter)
    db_exec(
        "INSERT INTO quick_infect_prefs(user_id, mode, chat_filter, updated_at) VALUES (?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET "
        "mode=excluded.mode, chat_filter=excluded.chat_filter, updated_at=excluded.updated_at",
        (int(user_id), str(m), str(f), int(now_ts())),
        commit=True
    )

def _quick_infect_mode_text(mode: str, chat_filter: str = "n") -> str:
    m, f = _normalize_quick_infect_pref(mode, chat_filter)

    if m == "r":
        return "Случайная цель"
    if m == "p":
        return "Случайная цель с большим био-опытом"
    if m == "m":
        return "Случайная цель с меньшим био-опытом"
    if m == "e":
        return "Случайная цель с равным био-опытом"

    if f == "p":
        return "Случайная цель из чата с большим био-опытом"
    if f == "m":
        return "Случайная цель из чата с меньшим био-опытом"
    if f == "e":
        return "Случайная цель из чата с равным био-опытом"
    return "Случайная цель из чата"

def _parse_quick_infect_pref_args(args: str) -> tuple[Optional[str], str, str]:
    s = (args or "").strip()
    if not s:
        return None, "n", ""

    toks = s.split()
    key = toks[0].lower()
    mode = INF_MODE_SYNONYMS.get(key)
    if not mode:
        return None, "n", "📑 Укажите режим патронов: <code>р</code> / <code>+</code> / <code>-</code> / <code>=</code> / <code>чат</code>"

    if mode != "c":
        if len(toks) > 1:
            return None, "n", "📑 Для этого режима указывается только одна переменная: <code>р</code> / <code>+</code> / <code>-</code> / <code>=</code>"
        return mode, "n", ""

    flt = "n"
    if len(toks) >= 2:
        flt = INF_CHAT_FILTER_SYNONYMS.get(toks[1].lower(), "")
        if not flt:
            return None, "n", "📑 Для режима <code>чат</code> допустимы только фильтры: <code>+</code> / <code>-</code> / <code>=</code>"

    if len(toks) > 2:
        return None, "n", "📑 Для режима <code>чат</code> допустима только одна дополнительная переменная: <code>+</code> / <code>-</code> / <code>=</code>"

    return mode, flt or "n", ""

def _pathogens_ui_data(uid: int, kind: str, count: int = 1, mode: str = "", chat_filter: str = "n") -> str:
    if str(kind or "") != "R":
        return f"PATHUI:{int(uid)}:{kind}:{int(count)}"

    m, f = _normalize_quick_infect_pref(mode, chat_filter)
    return f"PATHUI:{int(uid)}:{kind}:{int(count)}:{m}:{f}"

def _pathogens_ui_parse(data: str):
    try:
        p = (data or "").split(":")
        if not p or p[0] != "PATHUI":
            return None

        if len(p) == 4:
            return {
                "owner_id": int(p[1]),
                "kind": str(p[2]),
                "count": int(p[3]),
                "mode": "",
                "chat_filter": "n",
            }

        if len(p) == 6:
            return {
                "owner_id": int(p[1]),
                "kind": str(p[2]),
                "count": int(p[3]),
                "mode": str(p[4]),
                "chat_filter": str(p[5]),
            }

        return None
    except Exception:
        return None

def kb_pathogens(uid: int) -> InlineKeyboardMarkup:
    mode, chat_filter = get_quick_infect_pref(int(uid))

    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb(
            "Провести быстрое заражение",
            callback_data=_pathogens_ui_data(uid, "R", 1, mode, chat_filter),
            style="success"
        )
    )
    kb.row(
        _ikb("× 2", callback_data=_pathogens_ui_data(uid, "R", 2, mode, chat_filter), style="success"),
        _ikb("× 5", callback_data=_pathogens_ui_data(uid, "R", 5, mode, chat_filter), style="success"),
        _ikb("× 10", callback_data=_pathogens_ui_data(uid, "R", 10, mode, chat_filter), style="success"),
    )
    return kb

def render_pathogens_info(uid: int) -> str:
    ensure_lab_exists(int(uid))
    lab = get_lab(int(uid))
    pathogen_name = (lab["pathogen_name"] or "").strip() or "неизвестный патоген"
    mode, chat_filter = get_quick_infect_pref(int(uid))

    lines = []
    lines.append("📋 Краткая сводка")
    lines.append(f'🏷 Имя патогена: {h(pathogen_name)}')
    lines.append(f'🎯 {_quick_infect_mode_text(mode, chat_filter)}')
    lines.append("")
    lines.append(f'🧪 Кол-во патогенов: {int(lab["ready_pathogens"] or 0)} из {int(lab["total_pathogens"] or 0)}')
    npi = int(lab["next_pathogen_in"] or 0)
    if npi > 0:
        lines.append(f'⏱️ Новый патоген через {_format_hms(npi)}')
    else:
        lines.append('⏱️ Достигнут лимит производства')

    return "\n".join(lines)

def kb_pathogen_info(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=4)
    kb.row(
        _ikb_premium_icon_only("🦠", callback_data=_upg_cb("P", uid, "INF", 1, "PB")),
        _ikb_premium_icon_only("☠️", callback_data=_upg_cb("P", uid, "LET", 1, "PB")),
        _ikb_premium_icon_only("🧿", callback_data=_upg_cb("P", uid, "HEA", 1, "PB")),
        _ikb_premium_icon_only("🛡️", callback_data=_upg_cb("P", uid, "IMM", 1, "PB")),
    )
    return kb

def render_pathogen_brief(uid: int) -> str:
    ensure_lab_exists(int(uid))
    lab = get_lab(int(uid))
    pathogen_name = (lab["pathogen_name"] or "").strip() or "неизвестный патоген"

    lines = []
    lines.append("📋 Краткая сводка")
    lines.append(f'🏷 Имя патогена: {h(pathogen_name)}')
    lines.append(f'🦠 Заразность: {int(lab["infectivity"] or 0)} ур')
    lines.append(f'☠️ Летальность: {int(lab["lethality"] or 0)} ур')
    lines.append(f'🧿 Тяжесть: {int(lab["heaviness"] or 0)} ур')
    lines.append(f'🛡 Иммунитет: {int(lab["immunity"] or 0)} ур')
    return "\n".join(lines)

#             вакцина
def get_fever_and_vaccines(user_id: int) -> tuple[int, str, int]:
    uid = int(user_id)
    _merge_placeholder_for_uid_if_possible(uid)
    ensure_lab_exists(uid)

    r = db_one(
        "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(fever_pathogen,'') AS fp, COALESCE(ready_vaccines,0) AS v "
        "FROM labs WHERE user_id=?",
        (uid,)
    )
    if not r:
        return 0, "", 0
    return int(r["f"] or 0), (r["fp"] or ""), int(r["v"] or 0)

def _vaccine_fail_pct(target_id: int) -> float:
    uid = int(target_id)
    now = now_ts()

    qrow = db_one("SELECT COALESCE(qualification,1) AS q FROM labs WHERE user_id=?", (uid,))
    qual = int(qrow["q"] if qrow else 1) or 1

    hrow = db_one(
        "SELECT MAX(COALESCE(l.heaviness,0)) AS h "
        "FROM infections i "
        "JOIN labs l ON l.user_id=i.attacker_id "
        "WHERE i.target_id=? AND i.end_ts>?",
        (uid, now)
    )
    heavy = int(hrow["h"] if hrow and hrow["h"] is not None else 0)

    p_success, _ = _calc_heaviness_success_fail_pct(heavy, qual)
    return float(p_success)

def kb_vaccine_retry(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_counter("💉", "× 1", callback_data=_cb_use_vaccine_x(int(uid), 1), style="primary"),
        _ikb_premium_counter("💉", "× 5", callback_data=_cb_use_vaccine_x(int(uid), 5), style="primary"),
        _ikb_premium_counter("💉", "× 10", callback_data=_cb_use_vaccine_x(int(uid), 10), style="primary"),
    )
    return kb

def _vaccine_report_prefix(used: int) -> str:
    used = int(used)
    if used <= 1:
        return ""
    return f"📋 Отчёт об использовании вакцины:\nИспользовано вакцин: {used}\n\n"

def try_buy_vaccine(user_id: int) -> tuple[str, int, int]:
    """
    returns (status, spent_res, spent_mat)
    status: "OK" | "FAIL" | "NO_FEVER" | "NO_MONEY"
    """
    uid = int(user_id)
    now = now_ts()
    _merge_placeholder_for_uid_if_possible(uid)
    ensure_lab_exists(uid)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            row = c.execute(
                "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m "
                "FROM labs WHERE user_id=?",
                (uid,)
            ).fetchone()

            fever_until = int(row["f"] if row else 0)
            if fever_until <= now:
                conn.rollback()
                return "NO_FEVER", 0, 0

            res = int(row["r"] if row else 0)
            mat = int(row["m"] if row else 0)

            need = get_vaccine_price(uid)
            spent_res = 0
            spent_mat = 0

            if res >= need:
                spent_res = need
            else:
                if res > 0:
                    shortage = need - res
                    if mat >= shortage:
                        spent_res = res
                        spent_mat = shortage
                    else:
                        conn.rollback()
                        return "NO_MONEY", 0, 0
                else:
                    if mat >= need:
                        spent_mat = need
                    else:
                        conn.rollback()
                        return "NO_MONEY", 0, 0

            new_res = res - spent_res
            new_mat = mat - spent_mat

            fail_pct = _vaccine_fail_pct(uid)
            failed = (fail_pct > 0 and random.randint(1, 100) <= fail_pct)
            
            if failed:
                c.execute(
                    "UPDATE labs SET all_bio_res=?, all_bio_mater=? WHERE user_id=?",
                    (new_res, new_mat, uid)
                )
                conn.commit()
                return "FAIL", spent_res, spent_mat
            
            c.execute(
                "UPDATE labs SET all_bio_res=?, all_bio_mater=?, fever_until_ts=0, fever_pathogen='' WHERE user_id=?",
                (new_res, new_mat, uid)
            )
            conn.commit()
            return "OK", spent_res, spent_mat
        
        except Exception:
            conn.rollback()
            raise
        finally:
            try: c.close()
            except Exception: pass

def vaccine_spent_text(spent_res: int, spent_mat: int) -> str:
    if spent_res > 0 and spent_mat == 0:
        return _fmt_bio_res(spent_res)
    if spent_res == 0 and spent_mat > 0:
        return _fmt_bio_mater(spent_mat)
    return f"{_fmt_bio_res(spent_res)} + {_fmt_bio_mater(spent_mat)}"

def try_use_vaccine(user_id: int, doses: int = 1) -> tuple[str, int]:
    """
    returns: (status, used)
    status: "OK" | "FAIL" | "NO_FEVER" | "NO_VACCINE"
    used: сколько вакцин реально потрачено
    """
    uid = int(user_id)
    now = now_ts()
    _merge_placeholder_for_uid_if_possible(uid)
    ensure_lab_exists(uid)

    try:
        doses = int(doses)
    except Exception:
        doses = 1
    doses = max(1, min(10, doses))

    used = 0

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            row = c.execute(
                "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(ready_vaccines,0) AS v "
                "FROM labs WHERE user_id=?",
                (uid,)
            ).fetchone()

            fever_until = int(row["f"] if row else 0)
            v = int(row["v"] if row else 0)

            if fever_until <= now:
                conn.rollback()
                return "NO_FEVER", 0

            if v <= 0:
                conn.rollback()
                return "NO_VACCINE", 0

            fail_pct = _vaccine_fail_pct(uid)

            cured = False
            for _ in range(doses):
                if v <= 0:
                    break
                v -= 1
                used += 1

                if fail_pct > 0 and random.randint(1, 100) <= fail_pct:
                    continue

                cured = True
                break

            if cured:
                c.execute(
                    "UPDATE labs SET ready_vaccines=?, fever_until_ts=0, fever_pathogen='' WHERE user_id=?",
                    (v, uid)
                )
                conn.commit()
                return "OK", used

            c.execute("UPDATE labs SET ready_vaccines=? WHERE user_id=?", (v, uid))
            conn.commit()
            return ("FAIL" if used > 0 else "NO_VACCINE"), used

        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _parse_use_vaccine_args(message, parsed: "Parsed") -> tuple[int, Optional[int], object]:
    """
    Возвращает:
      doses, target_id, target_user_obj

    Поддержка:
      использовать вакцину
      использовать вакцину 5
      использовать вакцину @user
      использовать вакцину 5 @user
      reply + использовать вакцину
      reply + использовать вакцину 5
    """
    args = (parsed.args or "").strip()
    if not args:
        return 1, None, None

    parts = args.split(None, 1)
    doses = 1
    tail = args

    if parts and parts[0].isdigit():
        doses = int(parts[0])
        tail = parts[1].strip() if len(parts) > 1 else ""

    doses = max(1, min(10, int(doses)))

    if not tail:
        return doses, None, None

    fake = Parsed(
        raw=parsed.raw,
        has_prefix_char=parsed.has_prefix_char,
        prefix_char=parsed.prefix_char,
        cmd=parsed.cmd,
        args=tail
    )
    target_id, target_user_obj = resolve_target_from_reply_or_args(message, fake)
    return doses, target_id, target_user_obj

def try_use_vaccine_for_target(actor_id: int, target_id: int, doses: int = 1) -> tuple[str, int]:
    """
    actor_id  — у кого списываем ready_vaccines
    target_id — кого лечим от горячки

    returns: (status, used)
    status: "OK" | "FAIL" | "NO_FEVER" | "NO_VACCINE" | "NOT_SAME_CORP" | "BAD_TARGET"
    used: сколько вакцин реально потрачено
    """
    actor_id = int(actor_id)
    target_id = int(target_id)

    if actor_id <= 0 or target_id <= 0:
        return "BAD_TARGET", 0

    if actor_id == target_id:
        return try_use_vaccine(actor_id, doses)

    if not same_corp(actor_id, target_id):
        return "NOT_SAME_CORP", 0

    now = now_ts()
    _merge_placeholder_for_uid_if_possible(actor_id)
    _merge_placeholder_for_uid_if_possible(target_id)
    ensure_lab_exists(actor_id)
    ensure_lab_exists(target_id)

    try:
        doses = int(doses)
    except Exception:
        doses = 1
    doses = max(1, min(10, doses))

    used = 0

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            actor_row = c.execute(
                "SELECT COALESCE(ready_vaccines,0) AS v FROM labs WHERE user_id=?",
                (actor_id,)
            ).fetchone()
            target_row = c.execute(
                "SELECT COALESCE(fever_until_ts,0) AS f FROM labs WHERE user_id=?",
                (target_id,)
            ).fetchone()

            v = int(actor_row["v"] if actor_row else 0)
            fever_until = int(target_row["f"] if target_row else 0)

            if fever_until <= now:
                conn.rollback()
                return "NO_FEVER", 0

            if v <= 0:
                conn.rollback()
                return "NO_VACCINE", 0

            fail_pct = _vaccine_fail_pct(target_id)
            cured = False

            for _ in range(doses):
                if v <= 0:
                    break
                v -= 1
                used += 1

                if fail_pct > 0 and random.randint(1, 100) <= fail_pct:
                    continue

                cured = True
                break

            if cured:
                c.execute(
                    "UPDATE labs SET ready_vaccines=? WHERE user_id=?",
                    (int(v), actor_id)
                )
                c.execute(
                    "UPDATE labs SET fever_until_ts=0, fever_pathogen='' WHERE user_id=?",
                    (target_id,)
                )
                conn.commit()
                return "OK", int(used)

            c.execute(
                "UPDATE labs SET ready_vaccines=? WHERE user_id=?",
                (int(v), actor_id)
            )
            conn.commit()
            return "FAIL", int(used)

        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

#              приватность
def handle_privacy_toggle(message, cmd: str):
    uid = int(message.from_user.id)
    ensure_lab_exists(uid)

    if cmd == "balance_hide":
        set_hide_balance(uid, True)
        bot.reply_to(message, "✅ Баланс скрыт.")
        return
    if cmd == "balance_show":
        set_hide_balance(uid, False)
        bot.reply_to(message, "✅ Баланс открыт.")
        return
    if cmd == "lab_hide":
        set_hide_lab(uid, True)
        bot.reply_to(message, "✅ Досье лаборатории скрыто.")
        return
    if cmd == "lab_show":
        set_hide_lab(uid, False)
        bot.reply_to(message, "✅ Досье лаборатории открыто.")
        return

#             уведомления
def handle_notify_toggle(message, cmd: str):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    if cmd == "notify_on":
        if message.chat.type in ("group", "supergroup"):
            chat_id = int(message.chat.id)
            ok = True
            try:
                me = bot.get_me()
                cm = bot.get_chat_member(chat_id, me.id)
                st = (getattr(cm, "status", "") or "").lower()
                if st in ("left", "kicked"):
                    ok = False
                if hasattr(cm, "can_send_messages") and cm.can_send_messages is False:
                    ok = False
            except Exception:
                ok = True

            if not ok:
                set_notify_prefs(uid, 0, 0)
                bot.reply_to(message, "⚠️ Я не могу отправлять сообщения в этот чат. Уведомления будут приходить в личные сообщения.")
            else:
                set_notify_prefs(uid, chat_id, 0)
                bot.reply_to(message, "✅ Уведомления о заражении включены для этого чата.")
        else:
            set_notify_prefs(uid, 0, 0)
            bot.reply_to(message, "✅ Уведомления о заражении включены в личных сообщениях.")
        return

    chat_id, off = get_notify_prefs(uid)
    if message.chat.type in ("group", "supergroup"):
        set_notify_prefs(uid, 0, 0)
        bot.reply_to(message, "❎ Уведомления о заражении для этого чата отключены.")
        return

    if int(chat_id) == 0:
        set_notify_prefs(uid, 0, 1)
        bot.reply_to(message, "❎ Уведомления о заражении отключены.")
    else:
        bot.reply_to(message, "ℹ️ Уведомления уже включены для группового чата.")

def handle_user_pref_command(message, parsed: Parsed):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    if parsed.cmd == "corp_notify_on":
        _cid, _cname, role = _user_corp_role_soft(int(uid))
        if int(_cid) <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        set_corp_notify_enabled(int(uid), 1)
        bot.reply_to(message, "✅ Корпоративные уведомления включены.")
        return

    if parsed.cmd == "corp_notify_off":
        _cid, _cname, role = _user_corp_role_soft(int(uid))
        if int(_cid) <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        set_corp_notify_enabled(int(uid), 0)
        bot.reply_to(message, "❎ Корпоративные уведомления отключены.")
        return

    if parsed.cmd == "rp_on":
        set_rp_commands_enabled(int(uid), 1)
        bot.reply_to(message, "✅ Использование РП-команд включено.")
        return

    if parsed.cmd == "rp_off":
        set_rp_commands_enabled(int(uid), 0)
        bot.reply_to(message, "❎ Использование РП-команд отключено.")
        return

    if parsed.cmd == "gender_set":
        val = (parsed.args or "").strip().lower()

        if val in ("м", "муж", "мужской"):
            set_user_gender(int(uid), "male")
            bot.reply_to(message, "✅ Ваш пол изменён на мужской.")
            return

        if val in ("ж", "жен", "женский"):
            set_user_gender(int(uid), "female")
            bot.reply_to(message, "✅ Ваш пол изменён на женский.")
            return

        bot.reply_to(
            message,
            "📑 Используйте:\n"
            "<code>Мой пол м</code> / <code>Мой пол муж</code> / <code>Мой пол мужской</code>\n"
            "или\n"
            "<code>Мой пол ж</code> / <code>Мой пол жен</code> / <code>Мой пол женский</code>",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

#             автоответчик
def handle_autoanswer_toggle(message, cmd: str):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    now = now_ts()
    st = _auto_state(uid)
    enabled_at = int(st["enabled_at"] or 0) if st else 0
    reset_at = int(st["reset_at"] or 0) if st else 0

    if cmd == "autoanswer_status":
        text = render_autoanswer_status(uid)
        bot.send_message(
            message.chat.id,
            text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_autoanswer_status(uid)
        )
        return

    if cmd == "autoanswer_on":
        if enabled_at <= 0:
            enabled_at = now
        if reset_at <= 0 or reset_at <= now:
            reset_at = now + 86400
        db_exec(
            "UPDATE autoanswer_state SET enabled=1, enabled_at=?, reset_at=? WHERE user_id=?",
            (int(enabled_at), int(reset_at), int(uid)),
            commit=True
        )
        bot.send_message(
            message.chat.id,
            "✅ Автоответчик включён.",
            disable_web_page_preview=True,
            reply_markup=kb_autoanswer_open(uid)
        )
        return

    if cmd == "autoanswer_off":
        db_exec("UPDATE autoanswer_state SET enabled=0 WHERE user_id=?", (int(uid),), commit=True)
        bot.send_message(
            message.chat.id,
            "❎ Автоответчик выключен.",
            disable_web_page_preview=True,
            reply_markup=kb_autoanswer_open(uid)
        )
        return

# COMMANDS
@bot.message_handler(commands=["start"])
def cmd_start(message):
    if message.chat.type != "private":
        return
    try:
        if not is_channel_sender_message(message):
            upsert_user(message.from_user)
            _merge_placeholder_to_real_user(message.from_user)
        handle_help_command(message)
    except Exception as e:
        send_error_report("cmd_start", e)

# MEMBER BOT HANDLERS
@bot.message_handler(content_types=["new_chat_members"])
def on_new_chat_members(message):
    try:
        if message.chat.type in ("group", "supergroup"):
            remember_chat_member(message.chat.id, message.from_user)
            for u in (message.new_chat_members or []):
                remember_chat_member(message.chat.id, u)

        bot_id = getattr(_me, "id", None) if "_me" in globals() else None
        if bot_id and any(getattr(u, "id", 0) == bot_id for u in (message.new_chat_members or [])):
            sync_chat_admins(message.chat.id)
            txt = (
                f"✅ Я так рад, что меня добавили. Я - бот для игры заражений, {h(BOT_TITLE)}.\n"
                f"🔬Для вашего удобства в пользовании ботом, рекомендую ознакомиться со "
                f'<a href="{h(URL_COMMANDS)}">списком всех команд</a>.\n\n'
                "⚪️ В целях безопасности от спама и стабильной работы в боте по умолчанию установлен лимит на ответ в 2-3 секунды\n"
                "❗Для более корректной работы команд и обновления списков чата, рекомендую выдать мне приписку администратора. Права администратора выдавать не обязательно.\n\n"
                f'Остались вопросы? Можете обратиться в <a href="{h(URL_SUPPORT_CHAT)}">наш официальный чат тех.поддержки</a>.'
            )
            bot.send_message(message.chat.id, txt, disable_web_page_preview=True)
    except Exception as e:
        send_error_report("on_new_chat_members", e)

@bot.message_handler(content_types=["left_chat_member"])
def on_left_chat_member(message):
    try:
        if message.chat.type not in ("group", "supergroup"):
            return

        u = getattr(message, "left_chat_member", None)
        if not u:
            return

        uid = int(getattr(u, "id", 0) or 0)
        cid = int(message.chat.id)

        db_exec("DELETE FROM chat_members WHERE chat_id=? AND user_id=?", (cid, uid), commit=True)

        db_exec(
            "UPDATE users SET notify_chat_id=0, notify_off=0 WHERE user_id=? AND notify_chat_id=?",
            (uid, cid),
            commit=True
        )
    except Exception as e:
        send_error_report("on_left_chat_member", e)

@bot.chat_member_handler()
def on_chat_member_update(update):
    """
    Ловит изменения статуса участников (join/left/kicked/restricted/promoted…).
    Для получения таких апдейтов бот обычно должен быть админом чата.
    """
    try:
        chat = getattr(update, "chat", None)
        if not chat:
            return
        chat_id = int(getattr(chat, "id", 0) or 0)
        if chat_id == 0:
            return

        new_cm = getattr(update, "new_chat_member", None)
        if not new_cm:
            return

        u = getattr(new_cm, "user", None)
        if not u:
            return

        remember_chat_member(chat_id, u)

        status = (getattr(new_cm, "status", "") or "").lower()
        if status in ("left", "kicked"):
            uid = int(getattr(u, "id", 0) or 0)
            db_exec("DELETE FROM chat_members WHERE chat_id=? AND user_id=?", (chat_id, uid), commit=True)
            db_exec(
                "UPDATE users SET notify_chat_id=0, notify_off=0 WHERE user_id=? AND notify_chat_id=?",
                (uid, chat_id),
                commit=True
            )
    except Exception as e:
        send_error_report("on_chat_member_update", e)

@bot.my_chat_member_handler()
def on_my_chat_member_update(update):
    """
    Ловит изменения статуса БОТА в чате/ЛС.
    - В ЛС: фиксируем user_id (chat.id == user_id)
    - В группе/супергруппе: ведём список чатов, куда бот добавлен
    - Если бота удалили/он вышел — помечаем чат неактивным и сбрасываем привязки
    """
    try:
        chat = getattr(update, "chat", None)
        if not chat:
            return

        chat_id = int(getattr(chat, "id", 0) or 0)
        chat_type = (getattr(chat, "type", "") or "").lower()
        chat_title = (
            getattr(chat, "title", None)
            or getattr(chat, "full_name", None)
            or getattr(chat, "first_name", None)
            or ""
        )

        new_cm = getattr(update, "new_chat_member", None)
        status = (getattr(new_cm, "status", "") or "").lower() if new_cm else ""

        if chat_type in ("group", "supergroup"):
            if status in ("left", "kicked"):
                remember_bot_group_chat(chat_id, title=chat_title, chat_type=chat_type, is_active=0)
                try:
                    db_exec("DELETE FROM chat_members WHERE chat_id=?", (chat_id,), commit=True)
                except Exception:
                    pass
                try:
                    db_exec(
                        "UPDATE users SET notify_chat_id=0, notify_off=0 WHERE notify_chat_id=?",
                        (chat_id,),
                        commit=True
                    )
                except Exception:
                    pass
                return

            if status in ("member", "administrator"):
                remember_bot_group_chat(chat_id, title=chat_title, chat_type=chat_type, is_active=1)

        if chat_type == "private":
            fake_user = type("U", (), {})()
            fake_user.id = chat_id
            fake_user.username = None
            fake_user.first_name = None
            fake_user.last_name = None
            upsert_user(fake_user)
            set_pm_opened(int(chat_id), 1)
            set_notify_prefs(int(chat_id), 0, 0)

    except Exception as e:
        send_error_report("on_my_chat_member_update", e)

# CALLBACK HANDLERS
@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_BUY_VACCINE}:"))
def cb_buy_vaccine(cq):
    try:
        uid = int(cq.from_user.id)
        parts = (cq.data or "").split(":")
        target_uid = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else uid
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return
        upsert_user(cq.from_user)
        _merge_placeholder_for_uid_if_possible(cq.from_user)

        fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
        now = now_ts()

        if fever_until <= now:
            text = "📝 У вас нет горячки. Нет необходимости покупать вакцину."
            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text, 
                    chat_id=cq.message.chat.id, 
                    msg_id=cq.message.message_id,
                    parse_mode="HTML", 
                    reply_markup=None,
                    disable_web_page_preview=True
                )
            if cq.message:
                limited_edit_message_text(
                    text=text, 
                    chat_id=cq.message.chat.id, 
                    msg_id=cq.message.message_id,
                    parse_mode="HTML", 
                    reply_markup=None,
                    disable_web_page_preview=True
                )
            bot.answer_callback_query(cq.id)
            return

        if vac_cnt > 0:
            rm = InlineKeyboardMarkup()
            rm.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=_cb_use_vaccine(uid)), style="primary")
            text = (
                "💉 У вас нет необходимости покупать вакцину. Для быстрого выздоровления используйте вакцину\n"
                "команда \"<code>Био использовать вакцину</code>\""
            )
            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text, 
                    chat_id=cq.message.chat.id, 
                    msg_id=cq.message.message_id,
                    parse_mode="HTML", 
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            elif cq.message:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            bot.answer_callback_query(cq.id)
            return

        status, spent_res, spent_mat = try_buy_vaccine(uid)
        rm = None
        if status == "NO_FEVER":
            text = "📝 У вас нет горячки. Нет необходимости покупать вакцину."
        elif status == "NO_MONEY":
            source_chat_id = int(getattr(getattr(cq, "message", None), "chat", None).id) if getattr(cq, "message", None) and getattr(cq.message, "chat", None) else 0
            source_message_id = int(getattr(getattr(cq, "message", None), "message_id", 0) or 0)
            set_balance_chain_state(
                int(uid),
                BALCHAIN_VACCINE,
                "Повторить покупку",
                {"action": "buy"},
                source_chat_id=source_chat_id,
                source_message_id=source_message_id
            )
            text = "📝 У вас недостаточно средств."
            rm = kb_open_balance(int(uid))
        elif status == "FAIL":
            clear_balance_chain_state(int(uid))
            text = VACCINE_FAIL_TEXT
            rm = kb_vaccine_retry(uid)
        else:
            clear_balance_chain_state(int(uid))
            text = (
                "💉 Вакцина излечила вас от горячки.\n"
                f"🧾 Потрачено {vaccine_spent_text(spent_res, spent_mat)}"
            )

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        if cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_buy_vaccine", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_USE_VACCINE}:"))
def cb_use_vaccine(cq):
    try:
        uid = int(cq.from_user.id)
        parts = (cq.data or "").split(":")
        target_uid = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else uid
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return
        upsert_user(cq.from_user)
        _merge_placeholder_for_uid_if_possible(cq.from_user)

        fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
        now = now_ts()

        if fever_until <= now:
            text = "📝 У вас нет горячки. Нет необходимости использовать вакцину."
            rm = None
        else:
            status, used = try_use_vaccine(uid, 1)
            if status == "OK":
                text = "💉 Вакцина излечила вас от горячки.\n🧾 Потрачена 1 единица вакцины"
                rm = None
            elif status == "FAIL":
                text = VACCINE_FAIL_TEXT
                rm = kb_vaccine_retry(uid)
            elif status == "NO_VACCINE":
                price_txt = _fmt_bio_res(get_vaccine_price(uid))
                text = (
                    "💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: "
                    f"{price_txt}, команда \"<code>Био купить вакцину</code>\""
                )
                rm = InlineKeyboardMarkup()
                rm.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=_cb_buy_vaccine(uid), style="primary"))
            else:
                text = "📝 У вас нет горячки. Нет необходимости использовать вакцину."
                rm = None

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )    
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_use_vaccine", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_USE_VACCINE_X}:"))
def cb_use_vaccine_x(cq):
    try:
        uid = int(cq.from_user.id)
        parts = (cq.data or "").split(":")
        target_uid = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else uid
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return
        upsert_user(cq.from_user)
        _merge_placeholder_for_uid_if_possible(cq.from_user)

        doses = 1
        try:
            doses = int((cq.data or "").split(":", 3)[3])
        except Exception:
            doses = 1
        doses = max(1, min(10, doses))

        fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
        now = now_ts()

        if fever_until <= now:
            text = "📝 У вас нет горячки. Нет необходимости использовать вакцину."
            rm = None
        else:
            status, used = try_use_vaccine(uid, doses)
            prefix = _vaccine_report_prefix(used)

            if status == "OK":
                unit = _ru_form(used, "единица вакцины", "единицы вакцины", "единиц вакцины")
                text = prefix + f"💉 Вакцина излечила вас от горячки.\n🧾 Потрачено {used} {unit}"
                rm = None
            elif status == "FAIL":
                text = prefix + VACCINE_FAIL_TEXT
                rm = kb_vaccine_retry(uid)
            elif status == "NO_VACCINE":
                price_txt = _fmt_bio_res(get_vaccine_price(uid))
                text = prefix + (
                    "💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: "
                    f"{price_txt}, команда \"<code>Био купить вакцину</code>\""
                )
                rm = InlineKeyboardMarkup()
                rm.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=_cb_buy_vaccine(uid), style="primary"))
            else:
                text = "📝 У вас нет горячки. Нет необходимости использовать вакцину."
                rm = None

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_use_vaccine_x", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_AO_MENU}:"))
def cb_autoanswer_menu(cq):
    try:
        uid = int(cq.from_user.id)
        parts = (cq.data or "").split(":")
        tgt_uid = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else uid
        if tgt_uid != uid:
            bot.answer_callback_query(cq.id)
            return

        text = render_autoanswer_status(uid)
        rm = kb_autoanswer_status(uid)

        if cq.inline_message_id:
            limited_edit_message_text(text=text, inline_id=cq.inline_message_id, parse_mode="HTML",
                                      reply_markup=rm, disable_web_page_preview=True)
        else:
            limited_edit_message_text(text=text, chat_id=cq.message.chat.id, msg_id=cq.message.message_id,
                                      parse_mode="HTML", reply_markup=rm, disable_web_page_preview=True)
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_autoanswer_menu", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_AO_TOGGLE}:"))
def cb_autoanswer_toggle(cq):
    try:
        uid = int(cq.from_user.id)
        parts = (cq.data or "").split(":")
        tgt_uid = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else uid
        val = int(parts[3]) if len(parts) >= 4 and parts[3].isdigit() else 0
        if tgt_uid != uid:
            bot.answer_callback_query(cq.id)
            return

        now = now_ts()
        st = _auto_state(uid)
        enabled_at = int(st["enabled_at"] or 0) if st else 0
        reset_at = int(st["reset_at"] or 0) if st else 0

        if val == 1:
            if enabled_at <= 0:
                enabled_at = now
            if reset_at <= 0 or reset_at <= now:
                reset_at = now + 86400
            db_exec(
                "UPDATE autoanswer_state SET enabled=1, enabled_at=?, reset_at=? WHERE user_id=?",
                (int(enabled_at), int(reset_at), int(uid)),
                commit=True
            )
            text = "✅ Автоответчик включён."
        else:
            db_exec("UPDATE autoanswer_state SET enabled=0 WHERE user_id=?", (int(uid),), commit=True)
            text = "❎ Автоответчик выключен."

        rm = kb_autoanswer_open(uid)

        if cq.inline_message_id:
            limited_edit_message_text(text=text, inline_id=cq.inline_message_id, parse_mode="HTML",
                                      reply_markup=rm, disable_web_page_preview=True)
        else:
            limited_edit_message_text(text=text, chat_id=cq.message.chat.id, msg_id=cq.message.message_id,
                                      parse_mode="HTML", reply_markup=rm, disable_web_page_preview=True)
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_autoanswer_toggle", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{BALUI_TAG}:"))
def cb_balance_synth_ui(cq):
    try:
        uid, act, extra = _balui_parse(cq.data or "")
        if uid is None:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(uid):
            bot.answer_callback_query(cq.id)
            return

        if act == "R":
            force_attempt = (str(extra or "").strip().upper() == "S")
            if not _resume_balance_chain(cq, int(uid), force_attempt=force_attempt):
                bot.answer_callback_query(cq.id, "Повторить действие пока нельзя.", show_alert=False)
                return
            bot.answer_callback_query(cq.id)
            return

        if act == "S":
            text = synth_attempt(uid)
            rm = kb_synth(uid)
        elif act == "B":
            text = render_balance(uid)
            if str(extra or "").strip().upper() == "S":
                rm = kb_balance_after_synth(uid)
            else:
                rm = kb_balance_self(uid)
        else:
            bot.answer_callback_query(cq.id)
            return

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_balance_synth_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{INFUI_TAG}:"))
def cb_infect_retry(cq):
    try:
        info = _parse_infect_cb(cq.data or "")
        if not info:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(info.get("attacker", 0)):
            bot.answer_callback_query(cq.id)
            return

        class _P:
            cmd = "infect"
            has_prefix_char = False
            prefix_char = None
            raw = ""
            args = ""

        parsed = _P()

        if info["kind"] == "U":
            target_id = int(info["target"])
            count = int(info["count"])
            parsed.args = f"{target_id} {count}"
        else:
            mode = info["mode"]
            chat_filter = info["filter"]
            count = int(info["count"])

            if mode == "c":
                fl = "больше" if chat_filter == "p" else "меньше" if chat_filter == "m" else ""
                parsed.args = f"чат {count} {fl}".strip()
            elif mode == "r":
                parsed.args = f"р {count}"
            elif mode == "p":
                parsed.args = f"больше {count}"
            elif mode == "e":
                parsed.args = f"равный {count}"
            else:
                parsed.args = f"меньше {count}"

        class _FakeChat:
            pass

        class _FakeMsg:
            pass

        fm = _FakeMsg()
        fm.from_user = cq.from_user
        fm.reply_to_message = None
        fm.text = ""
        fm.via_bot = None
        fm.chat = _FakeChat()

        edit_ctx = None

        if cq.message:
            fm.chat = cq.message.chat
            fm.message_id = int(cq.message.message_id)
            fm.text = getattr(cq.message, "text", "") or ""
            edit_ctx = {"chat_id": cq.message.chat.id, "msg_id": cq.message.message_id}
        else:
            fm.chat.id = 0
            fm.chat.type = "inline"
            fm.message_id = 0
            edit_ctx = {"inline_id": cq.inline_message_id} if cq.inline_message_id else None

        handle_infect_command(
            fm,
            parsed,
            edit_ctx=edit_ctx,
            actor_user=cq.from_user
        )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_infect_retry", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith("PATHUI:"))
def cb_pathogens_ui(cq):
    try:
        info = _pathogens_ui_parse(cq.data or "")
        if not info:
            bot.answer_callback_query(cq.id)
            return

        owner_id = int(info["owner_id"])
        kind = str(info["kind"])
        count = int(info["count"])
        mode = str(info.get("mode") or "")
        chat_filter = str(info.get("chat_filter") or "n")

        if int(cq.from_user.id) != int(owner_id):
            bot.answer_callback_query(cq.id)
            return

        if kind == "INFO":
            text = render_pathogen_brief(int(owner_id))
            rm = kb_pathogen_info(int(owner_id))

            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            elif cq.message:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )

            bot.answer_callback_query(cq.id)
            return

        class _P:
            cmd = "infect"
            has_prefix_char = False
            prefix_char = None
            raw = ""
            args = ""

        parsed = _P()
        if kind == "R":
            if not mode:
                mode, chat_filter = get_quick_infect_pref(int(owner_id))

            mode, chat_filter = _normalize_quick_infect_pref(mode, chat_filter)

            if mode == "c":
                msg_chat = getattr(cq, "message", None)
                msg_chat_type = (getattr(getattr(msg_chat, "chat", None), "type", "") or "").lower()
                if msg_chat_type not in ("group", "supergroup"):
                    bot.answer_callback_query(cq.id, "📑 Режим «чат» нельзя использовать в личных сообщениях бота.", show_alert=True)
                    return

                fl = ""
                if chat_filter == "p":
                    fl = " больше"
                elif chat_filter == "m":
                    fl = " меньше"
                elif chat_filter == "e":
                    fl = " равный"

                parsed.args = f"чат {int(count)}{fl}".strip()

            elif mode == "p":
                parsed.args = f"больше {int(count)}"
            elif mode == "m":
                parsed.args = f"меньше {int(count)}"
            elif mode == "e":
                parsed.args = f"равный {int(count)}"
            else:
                parsed.args = f"р {int(count)}"

        class _FakeChat:
            pass

        class _FakeMsg:
            pass

        fm = _FakeMsg()
        fm.from_user = cq.from_user
        fm.reply_to_message = None
        fm.text = ""
        fm.via_bot = None
        fm.chat = _FakeChat()

        edit_ctx = {"pathogens_summary": True}

        if cq.message:
            fm.chat = cq.message.chat
            fm.message_id = int(cq.message.message_id)
            fm.text = getattr(cq.message, "text", "") or ""
            edit_ctx.update({"chat_id": cq.message.chat.id, "msg_id": cq.message.message_id})
        else:
            fm.chat.id = 0
            fm.chat.type = "inline"
            fm.message_id = 0
            if cq.inline_message_id:
                edit_ctx.update({"inline_id": cq.inline_message_id})

        handle_infect_command(
            fm,
            parsed,
            edit_ctx=edit_ctx,
            actor_user=cq.from_user
        )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_pathogens_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{LABUI_TAG}:"))
def cb_lab_ui(cq):
    try:
        owner_id, view = _labui_parse(cq.data or "")
        if owner_id is None:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(owner_id):
            bot.answer_callback_query(cq.id)
            return

        is_inline = bool(cq.inline_message_id)

        if view == "D":  # dossier
            text = render_lab(owner_id)
            rm = kb_lab_dossier_inline(owner_id) if is_inline else kb_lab_dossier(owner_id)
        elif view == "R":  # R&D
            text = render_lab_dev(owner_id)
            rm = kb_lab_dev_inline(owner_id) if is_inline else kb_lab_dev(owner_id)
        elif view == "S":  # security
            text = render_lab_sec(owner_id)
            rm = kb_lab_sec_inline(owner_id) if is_inline else kb_lab_sec(owner_id)
        elif view == "I":  # infected list
            text = render_lab_infected_list(owner_id)
            rm = kb_lab_infected_inline(owner_id) if is_inline else kb_lab_infected(owner_id)
        elif view == "B":  # diseases list
            text = render_lab_diseases_list(owner_id)
            rm = kb_lab_diseases_inline(owner_id) if is_inline else kb_lab_diseases(owner_id)
        else:
            bot.answer_callback_query(cq.id)
            return

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_lab_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_JOIN}:"))
def cb_corp_join(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) < 4:
            bot.answer_callback_query(cq.id)
            return
        _tag0, _tag1, corp_id_s, viewer_id_s = p[0], p[1], p[2], p[3]
        corp_id = int(corp_id_s)
        viewer_id = int(viewer_id_s)

        if int(cq.from_user.id) != int(viewer_id):
            bot.answer_callback_query(cq.id)
            return

        corp = corp_by_id(corp_id)
        if not corp:
            bot.answer_callback_query(cq.id)
            return

        if not is_lab_active(viewer_id):
            bot.answer_callback_query(cq.id)
            return

        my_cid, _ = get_user_corp(viewer_id)
        if my_cid > 0:
            bot.answer_callback_query(cq.id)
            return

        min_be = int(corp["min_bio_exp"] or 0)
        my_lab = get_lab(viewer_id)
        my_be = int(my_lab["bio_exp"] or 0)
        if min_be > 0 and my_be < min_be:
            bot.answer_callback_query(cq.id, f"📝 Недостаточно био-опыта. Порог вступления {_fmt_k(min_be)}.", show_alert=True)
            return

        if corp_is_open_value(corp) == 1:
            _corp_join_open(viewer_id, corp)
            _send_corp_join_notices(corp, viewer_id)

            who = _corp_actor_tag(viewer_id)
            txt = (
                f"✅ Вы приняты в Корпорацию {corp_name_display(corp['name'])}\n"
                f"Добро пожаловать в коллектив, {who}"
            )
            if getattr(cq, "message", None):
                bot.send_message(
                    int(cq.message.chat.id),
                    txt,
                    reply_to_message_id=int(cq.message.message_id),
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            bot.answer_callback_query(cq.id)
            return

        ex = db_one(
            "SELECT request_id FROM corp_requests WHERE corp_id=? AND user_id=? AND status='pending' ORDER BY request_id DESC LIMIT 1",
            (corp_id, viewer_id)
        )
        if ex:
            bot.answer_callback_query(cq.id)
            return

        if getattr(cq, "message", None):
            request_id = _create_corp_request(
                corp,
                viewer_id,
                user_chat_id=int(cq.message.chat.id),
                user_reply_to=int(cq.message.message_id),
                send_user_notice=False
            )

            if not cq.inline_message_id:
                db_exec(
                    "INSERT OR IGNORE INTO corp_request_msgs(request_id, chat_id, msg_id, kind) VALUES (?,?,?, 'user')",
                    (int(request_id), int(cq.message.chat.id), int(cq.message.message_id)),
                    commit=True
                )

            new_text = f"📄 Ваша заявка на вступление в Корпорацию {corp_name_display(corp['name'])} отправлена на рассмотрение."

            if cq.inline_message_id:
                limited_edit_message_text(
                    text=new_text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=None,
                    disable_web_page_preview=True
                )
            else:
                limited_edit_message_text(
                    text=new_text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=None,
                    disable_web_page_preview=True
                )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_corp_join", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_REQ_APPROVE}:"))
def cb_corp_req_approve(cq):
    try:
        request_id = int((cq.data or "").rsplit(":", 1)[1])
    except Exception:
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass
        return

    try:
        ok, msg = _corp_request_resolve(request_id, int(cq.from_user.id), True)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_corp_req_approve", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_REQ_REJECT}:"))
def cb_corp_req_reject(cq):
    try:
        request_id = int((cq.data or "").rsplit(":", 1)[1])
    except Exception:
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass
        return

    try:
        ok, msg = _corp_request_resolve(request_id, int(cq.from_user.id), False)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_corp_req_reject", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_INV_ACCEPT}:"))
def cb_corp_inv_accept(cq):
    try:
        invite_id = int((cq.data or "").rsplit(":", 1)[1])
    except Exception:
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass
        return

    try:
        ok, msg = _corp_invite_resolve(invite_id, int(cq.from_user.id), True)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_corp_inv_accept", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_INV_REJECT}:"))
def cb_corp_inv_reject(cq):
    try:
        invite_id = int((cq.data or "").rsplit(":", 1)[1])
    except Exception:
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass
        return

    try:
        ok, msg = _corp_invite_resolve(invite_id, int(cq.from_user.id), False)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_corp_inv_reject", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_CORP_TX}:"))
def cb_corp_transfer_mix(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 7:
            bot.answer_callback_query(cq.id)
            return

        _tag, action, uid_s, mode_s, target_id_s, res_s, mat_s = p
        uid = int(uid_s)
        target_id = int(target_id_s)
        res_amount = int(res_s)
        mat_amount = int(mat_s)
        cmd = _corp_transfer_cmd_from_mode(mode_s)

        if int(cq.from_user.id) != int(uid):
            bot.answer_callback_query(cq.id)
            return

        if cmd not in ("corp_send_res", "corp_send_mat") or target_id <= 0:
            bot.answer_callback_query(cq.id)
            return

        def _edit_current(text: str, rm=None):
            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            else:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )

        if str(action or "").upper() == "C":
            st = get_balance_chain_state(int(uid))
            if st and str(st.get("chain_kind") or "") == BALCHAIN_CORP_TRANSFER:
                clear_balance_chain_state(int(uid))
            _edit_current("📝 Перевод прерван.", rm=None)
            bot.answer_callback_query(cq.id)
            return

        ok, err = _corp_transfer_apply(
            int(uid),
            int(target_id),
            res_amount=int(res_amount),
            mat_amount=int(mat_amount)
        )

        if not ok:
            if err in ("📝 У вас нет столько био-ресурсов.", "📝 У вас нет столько био-материалов."):
                set_balance_chain_state(
                    int(uid),
                    BALCHAIN_CORP_TRANSFER,
                    "Повторить перевод",
                    {"cmd": cmd, "amount": int(res_amount + mat_amount), "target_id": int(target_id)},
                    source_chat_id=int(getattr(getattr(cq, "message", None), "chat", None).id) if getattr(cq, "message", None) and getattr(cq.message, "chat", None) else 0,
                    source_message_id=int(getattr(getattr(cq, "message", None), "message_id", 0) or 0)
                )
                _edit_current(err, rm=kb_open_balance(int(uid)))
            else:
                _edit_current(err, rm=None)

            bot.answer_callback_query(cq.id)
            return

        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_CORP_TRANSFER:
            clear_balance_chain_state(int(uid))

        _edit_current(
            _corp_transfer_success_text(int(target_id), int(res_amount), int(mat_amount)),
            rm=None
        )
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_corp_transfer_mix", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CORPUI_TAG}:"))
def cb_corpui(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) < 4:
            bot.answer_callback_query(cq.id)
            return

        _tag, act, corp_id_s, viewer_id_s = p[0], p[1], p[2], p[3]
        corp_id = int(corp_id_s)
        viewer_id = int(viewer_id_s)

        if int(cq.from_user.id) != int(viewer_id):
            bot.answer_callback_query(cq.id)
            return

        corp = corp_by_id(corp_id)
        if not corp:
            bot.answer_callback_query(cq.id)
            return

        notice_text = None

        if act == "M":
            if not corp_is_member(corp_id, viewer_id):
                bot.answer_callback_query(cq.id)
                return
            text, rm = render_corp_members_text(corp, viewer_id)

        elif act == "R":
            if not corp_is_owner_or_deputy(corp_id, viewer_id):
                bot.answer_callback_query(cq.id)
                return
            text, rm = render_corp_requests_text(corp, viewer_id)

        elif act in ("O", "C"):
            if not corp_is_owner_or_deputy(corp_id, viewer_id):
                bot.answer_callback_query(cq.id)
                return

            new_state = 1 if act == "O" else 0
            db_exec("UPDATE corps SET is_open=? WHERE corp_id=?", (new_state, corp_id), commit=True)

            corp = corp_by_id(corp_id)
            text, rm = render_corp_info_text(corp, viewer_id)
            notice_text = "Корпорация открыта." if new_state == 1 else "Корпорация закрыта."

        else:
            text, rm = render_corp_info_text(corp, viewer_id)

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        else:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        if notice_text:
            bot.answer_callback_query(cq.id, notice_text)
        else:
            bot.answer_callback_query(cq.id)

    except Exception as e:
        send_error_report("cb_corpui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{TOPUI_TAG}:"))
def cb_topui(cq):
    try:
        info = _topui_parse(cq.data or "")
        if not info:
            bot.answer_callback_query(cq.id)
            return

        kind = (info["kind"] or "").strip().upper()
        chat_id = int(info["chat_id"] or 0)
        limit = _top_limit_from_args(str(info["limit"] or 30))

        if kind == "U":
            text, rm = render_top_users(limit, chat_id)
        elif kind == "D":
            text, rm = render_top_diseases(limit, chat_id)
        elif kind == "C":
            text, rm = render_top_corps(limit, chat_id)
        else:
            bot.answer_callback_query(cq.id)
            return

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_topui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{SETUI_TAG}:"))
def cb_settings_ui(cq):
    try:
        uid, act = _settings_parse_cb(cq.data or "")
        if uid is None:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(uid):
            bot.answer_callback_query(cq.id)
            return

        if act in ("HB", "HL"):
            lab_row = db_one(
                "SELECT COALESCE(hide_balance,0) AS hb, COALESCE(hide_lab,0) AS hl, COALESCE(lab_active,0) AS la "
                "FROM labs WHERE user_id=? LIMIT 1",
                (int(uid),)
            )
            if not lab_row or int(lab_row["la"] or 0) != 1:
                bot.answer_callback_query(cq.id, "📑 У вас нет активной Лаборатории.", show_alert=True)
                return

            if act == "HB":
                set_hide_balance(int(uid), not bool(int(lab_row["hb"] or 0)))
            else:
                set_hide_lab(int(uid), not bool(int(lab_row["hl"] or 0)))

        elif act == "NPM":
            set_notify_prefs(int(uid), 0, 0)

        elif act == "NOFF":
            set_notify_prefs(int(uid), 0, 1)

        elif act == "NCHAT":
            if not cq.message or (cq.message.chat.type not in ("group", "supergroup")):
                bot.answer_callback_query(cq.id)
                return
            set_notify_prefs(int(uid), int(cq.message.chat.id), 0)

        elif act == "G":
            cur_g = get_user_gender(int(uid))
            set_user_gender(int(uid), "female" if cur_g == "male" else "male")

        elif act == "GM":
            set_user_gender(int(uid), "male")
        
        elif act == "GF":
            set_user_gender(int(uid), "female")

        elif act == "RP":
            cur = rp_commands_enabled(int(uid))
            set_rp_commands_enabled(int(uid), 0 if cur == 1 else 1)

        elif act == "CN":
            _cid, _cname, role = _user_corp_role_soft(int(uid))
            if int(_cid) <= 0:
                bot.answer_callback_query(cq.id, "📑 Вы не состоите в Корпорации.", show_alert=True)
                return
            cur = corp_notify_enabled(int(uid))
            set_corp_notify_enabled(int(uid), 0 if cur == 1 else 1)

        else:
            bot.answer_callback_query(cq.id)
            return

        current_chat_id = int(cq.message.chat.id) if cq.message else 0
        current_chat_type = (cq.message.chat.type if cq.message else "private")
        text = render_settings_text(int(uid), current_chat_id)
        rm = kb_settings(int(uid), current_chat_id, current_chat_type)

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_settings_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{REPORTUI_TAG}:"))
def cb_report_ui(cq):
    try:
        uid, act = _report_parse_cb(cq.data or "")
        if uid is None:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(uid):
            bot.answer_callback_query(cq.id)
            return

        if act not in REPORT_CATS:
            bot.answer_callback_query(cq.id)
            return

        if is_bot_banned(int(uid)) and act != "APPEAL":
            bot.answer_callback_query(cq.id, "Для заблокированных пользователей доступна только апелляция.", show_alert=True)
            return

        if act == "RESTORE" and not get_deleted_lab_row(int(uid)):
            bot.answer_callback_query(cq.id, "📑 У вас нет сохранённой лаборатории для восстановления.", show_alert=True)
            return

        report_set_state(int(uid), act, "await_content")
        text = _report_prompt(int(uid), act)

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_report_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{BLUI_TAG}:"))
def cb_blacklist_ui(cq):
    try:
        page = _blacklist_parse_cb(cq.data or "")
        if page is None:
            bot.answer_callback_query(cq.id)
            return

        if not is_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text, rm = render_blacklist_text(int(page))

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_blacklist_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{USERSUI_TAG}:"))
def cb_users_ui(cq):
    try:
        page = _users_parse_cb(cq.data or "")
        if page is None:
            bot.answer_callback_query(cq.id)
            return

        if not is_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text, rm = render_users_text(int(page))

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_users_ui", e)
        try:
            bot.answer_callback_query(cq.id, "Не удалось переключить страницу.")
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "") == _cof_inf_stats_cb())
def cb_cof_inf_stats_refresh(cq):
    try:
        if not can_manage_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text = render_cof_inf_stats_text()
        rm = kb_cof_inf_stats()

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id, "Статистика обновлена.")
    except Exception as e:
        send_error_report("cb_cof_inf_stats_refresh", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "") == _cof_duel_stats_cb())
def cb_duel_cof_stats_refresh(cq):
    try:
        if not can_manage_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text = render_duel_cof_stats_text()
        rm = kb_duel_cof_stats()

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id, "Статистика обновлена.")
    except Exception as e:
        send_error_report("cb_duel_cof_stats_refresh", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{DBFILEUI_TAG}:"))
def cb_db_file_export(cq):
    try:
        payload = _db_file_export_parse_cb(cq.data or "")
        if not payload:
            bot.answer_callback_query(cq.id)
            return

        uid = int(cq.from_user.id)
        target_uid = int(payload["user_id"])
        source_kind = (payload["source_kind"] or "").strip().upper()

        if uid != target_uid:
            bot.answer_callback_query(cq.id, "📑 Это не ваша кнопка.")
            return

        if not can_manage_support(uid):
            bot.answer_callback_query(cq.id)
            return

        ok, msg = _send_db_export_archive(int(uid), int(uid), source_kind)
        if not ok:
            try:
                bot.answer_callback_query(cq.id, msg[:180], show_alert=True)
            except Exception:
                bot.answer_callback_query(cq.id)
            return

        if cq.inline_message_id:
            limited_edit_message_text(
                text=msg,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=msg,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id, "Архив отправлен.")
    except Exception as e:
        send_error_report("cb_db_file_export", e)
        try:
            bot.answer_callback_query(cq.id, "Не удалось подготовить архив.")
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{DBSTATUI_TAG}:"))
def cb_db_file_stat(cq):
    try:
        payload = _dbstat_parse_cb(cq.data or "")
        if not payload:
            bot.answer_callback_query(cq.id)
            return

        uid = int(cq.from_user.id)
        target_uid = int(payload["user_id"])
        action = (payload["action"] or "").strip().upper()

        if uid != target_uid:
            bot.answer_callback_query(cq.id, "📑 Это не ваша кнопка.")
            return

        if not can_manage_support(uid):
            bot.answer_callback_query(cq.id)
            return

        if action == "RESET":
            row = _db_schedule_row(int(uid))
            if not row or int(row["next_run_ts"] or 0) <= 0:
                bot.answer_callback_query(cq.id, "📑 Автосэйв уже выключен.")
                return

            _db_schedule_clear(int(uid))
            text = render_db_file_stat_text(int(uid))
            rm = kb_db_file_stat(int(uid))

            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            elif cq.message:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )

            bot.answer_callback_query(cq.id, "Автосэйв сброшен.")
            return

        if action == "LIST":
            text = render_db_export_ids_text(int(uid))
            rm = kb_db_export_ids(int(uid))

            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            elif cq.message:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )

            bot.answer_callback_query(cq.id)
            return

        if action == "BACK":
            text = render_db_file_stat_text(int(uid))
            rm = kb_db_file_stat(int(uid))

            if cq.inline_message_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=cq.inline_message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )
            elif cq.message:
                limited_edit_message_text(
                    text=text,
                    chat_id=cq.message.chat.id,
                    msg_id=cq.message.message_id,
                    parse_mode="HTML",
                    reply_markup=rm,
                    disable_web_page_preview=True
                )

            bot.answer_callback_query(cq.id)
            return

        bot.answer_callback_query(cq.id)

    except Exception as e:
        send_error_report("cb_db_file_stat", e)
        try:
            bot.answer_callback_query(cq.id, "Не удалось выполнить действие.")
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CHATSUI_TAG}:"))
def cb_known_chats_ui(cq):
    try:
        page = _known_chats_parse_cb(cq.data or "")
        if page is None:
            bot.answer_callback_query(cq.id)
            return

        if not is_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text, rm = render_known_chats_text(int(page))

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_known_chats_ui", e)
        try:
            bot.answer_callback_query(cq.id, "Не удалось открыть список чатов.")
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{PROMOUI_TAG}:"))
def cb_promo_ui(cq):
    try:
        page = _promo_parse_cb(cq.data or "")
        if page is None:
            bot.answer_callback_query(cq.id)
            return
        if not can_manage_support(int(cq.from_user.id)):
            bot.answer_callback_query(cq.id)
            return

        text, rm = render_promocode_list_text(int(page))
        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_promo_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{EMPACKUI_TAG}:"))
def cb_emoji_pack_ui(cq):
    try:
        cache_key, page = _emoji_pack_parse_cb(cq.data or "")
        if not cache_key or page is None:
            bot.answer_callback_query(cq.id)
            return

        cached = _EMOJI_PACK_VIEW_CACHE.get(cache_key)
        if not cached:
            bot.answer_callback_query(cq.id, "Список эмодзи пака устарел. Вызовите команду снова.")
            return

        text, rm = render_emoji_pack_ids_page(
            str(cached.get("title") or ""),
            str(cached.get("url") or ""),
            list(cached.get("items") or []),
            int(page)
        )

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_emoji_pack_ui", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_RP_ACCEPT}:"))
def cb_rp_accept(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        offer_id = int(parts[2])
        row = db_one(
            "SELECT offer_id, actor_id, action_key, target_id, status, created_at, extra_tail, comment_text "
            "FROM rp_offers WHERE offer_id=? LIMIT 1",
            (int(offer_id),)
        )
        if not row:
            bot.answer_callback_query(cq.id)
            return

        actor_id = int(row["actor_id"])

        if rp_commands_enabled(int(actor_id)) != 1:
            bot.answer_callback_query(cq.id, "📑 У отправителя отключены РП-команды.", show_alert=True)
            return
        
        if rp_commands_enabled(int(cq.from_user.id)) != 1:
            bot.answer_callback_query(cq.id, "📑 У вас отключены РП-команды.", show_alert=True)
            return

        if int(cq.from_user.id) == actor_id:
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        if str(row["status"] or "") != "pending":
            bot.answer_callback_query(cq.id, "Кто не успел, тот опоздал.")
            return

        action = _resolve_rp_action_ref(str(row["action_key"]), actor_id)
        if not action:
            bot.answer_callback_query(cq.id)
            return

        db_exec(
            "UPDATE rp_offers SET target_id=?, status='accepted' WHERE offer_id=?",
            (int(cq.from_user.id), int(offer_id)),
            commit=True
        )

        upsert_user(cq.from_user)
        actor_tag = public_user_tag(actor_id)
        target_tag = _rp_actor_tag(cq.from_user)

        extra_tail = str(row["extra_tail"] or "").strip()
        comment_text = str(row["comment_text"] or "").strip()

        final_text = _rp_emit_action_text(
            action,
            int(actor_id),
            actor_tag,
            target_tag,
            extra_tail=extra_tail,
            comment_text=comment_text
        )

        _rp_insert_event(action["trigger_key"], actor_id, int(cq.from_user.id))
        _inc_personal_rp_use(action)

        if cq.inline_message_id:
            limited_edit_message_text(
                text=final_text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=final_text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_rp_accept", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_RP_DECLINE}:"))
def cb_rp_decline(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        offer_id = int(parts[2])
        row = db_one(
            "SELECT offer_id, actor_id, action_key, target_id, status, created_at "
            "FROM rp_offers WHERE offer_id=? LIMIT 1",
            (int(offer_id),)
        )
        if not row:
            bot.answer_callback_query(cq.id)
            return

        actor_id = int(row["actor_id"])
        if int(cq.from_user.id) == actor_id:
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        if str(row["status"] or "") != "pending":
            bot.answer_callback_query(cq.id, "Вы не успели.")
            return

        db_exec(
            "UPDATE rp_offers SET target_id=?, status='declined' WHERE offer_id=?",
            (int(cq.from_user.id), int(offer_id)),
            commit=True
        )

        upsert_user(cq.from_user)
        actor_tag = public_user_tag(actor_id)
        target_tag = _rp_actor_tag(cq.from_user)
        text = f"❌ {target_tag} {_gender_pick(int(cq.from_user.id), 'rp_reject')} предложение {actor_tag}."

        if cq.inline_message_id:
            limited_edit_message_text(
                text=text,
                inline_id=cq.inline_message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )
        elif cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=None,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id, "Мои сожаления, вам отказали 😔")
    except Exception as e:
        send_error_report("cb_rp_decline", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_LAB_DELETE_OK}:"))
def cb_lab_delete_ok(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 3:
            bot.answer_callback_query(cq.id)
            return

        target_uid = int(p[2])
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id)
            return

        ok, text = _perform_lab_delete(int(target_uid))
        out_text = build_inactive_lab_text(int(target_uid), after_delete=True) if ok else text
        rm = kb_inactive_lab_actions(int(target_uid)) if ok else None

        if cq.message:
            limited_edit_message_text(
                text=out_text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        bot.answer_callback_query(cq.id, "Лаборатория удалена." if ok else "Не удалось удалить лабораторию.", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_lab_delete_ok", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_LAB_DELETE_CANCEL}:"))
def cb_lab_delete_cancel(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 3:
            bot.answer_callback_query(cq.id)
            return

        target_uid = int(p[2])
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id)
            return

        clear_lab_delete_pending(int(target_uid))

        if cq.message:
            try:
                bot.delete_message(int(cq.message.chat.id), int(cq.message.message_id))
            except Exception:
                pass

        bot.answer_callback_query(cq.id, "Удаление отменено.")
    except Exception as e:
        send_error_report("cb_lab_delete_cancel", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_LAB_CREATE}:"))
def cb_lab_create(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 3:
            bot.answer_callback_query(cq.id)
            return

        target_uid = int(p[2])
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id)
            return

        if not is_lab_active(int(target_uid)):
            ensure_lab_exists(int(target_uid))
            if get_deleted_lab_row(int(target_uid)):
                _set_deleted_lab_restore_offer_suppressed(int(target_uid), True)
            mark_lab_active(int(target_uid))
            _maybe_apply_deleted_lab_bonus(int(target_uid))

        is_inline = bool(getattr(cq, "inline_message_id", None))
        text = render_lab(int(target_uid))
        rm = kb_lab_dossier_inline(int(target_uid)) if is_inline else kb_lab_dossier(int(target_uid))
        _lab_state_edit_current(cq, text, rm=rm)

        bot.answer_callback_query(cq.id, "Лаборатория создана.")
    except Exception as e:
        send_error_report("cb_lab_create", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_LAB_RESTORE}:"))
def cb_lab_restore(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 3:
            bot.answer_callback_query(cq.id)
            return

        target_uid = int(p[2])
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id)
            return

        ok, text = _restore_deleted_lab(int(target_uid), support_mode=False)
        if ok:
            is_inline = bool(getattr(cq, "inline_message_id", None))
            text = render_lab(int(target_uid))
            rm = kb_lab_dossier_inline(int(target_uid)) if is_inline else kb_lab_dossier(int(target_uid))
        else:
            rm = kb_inactive_lab_actions(int(target_uid))

        _lab_state_edit_current(cq, text, rm=rm)
        bot.answer_callback_query(cq.id, "Лаборатория восстановлена." if ok else "Не удалось восстановить лабораторию.", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_lab_restore", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_LAB_RESTORE_REQ}"))
def cb_lab_restore_req(cq):
    try:
        p = (cq.data or "").split(":")
        if len(p) != 4:
            bot.answer_callback_query(cq.id)
            return

        target_uid = int(p[3])
        if int(cq.from_user.id) != int(target_uid):
            bot.answer_callback_query(cq.id)
            return

        if not get_deleted_lab_row(int(target_uid)):
            bot.answer_callback_query(cq.id, "📑 Сохранённая лаборатория не найдена.", show_alert=True)
            return

        if cq.message and cq.message.chat.type == "private":
            report_clear_state(int(target_uid))
            report_set_state(int(target_uid), "RESTORE", "await_content")
            _lab_state_edit_current(cq, _report_prompt(int(target_uid), "RESTORE"), rm=None)
            bot.answer_callback_query(cq.id)
            return

        ok, info_text = _start_restore_report_flow_for_user(int(target_uid))
        _lab_state_edit_current(
            cq,
            info_text,
            rm=kb_open_bot_pm() if not ok else None
        )
        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_lab_restore_req", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

# DUELS
#        CALLBACKS
CB_DUEL_ACCEPT = "DUEL_ACCEPT"
CB_DUEL_DECLINE = "DUEL_DECLINE"
CB_DUEL_FIRE = "DUEL_FIRE"
CB_DUEL_AIM = "DUEL_AIM"
CB_DUEL_BREAK_AIM = "DUEL_BREAK_AIM"
CB_DUEL_SURRENDER = "DUEL_SURRENDER"
CB_DUEL_CANCEL = "DUEL_CANCEL"
CB_DUEL_INV_CANCEL = "DUEL_INV_CANCEL"
CB_DUEL_REMATCH = "DUEL_REMATCH"
CB_DUEL_RANDOM = "DUEL_RANDOM"
#         CONSTANTS
DUEL_INVITE_TIMEOUT_SEC = 5 * 60
DUEL_TURN_TIMEOUT_SEC = 5 * 60
DUEL_BASE_HIT_PCT = 20
DUEL_MAX_TURNS = 40
DUEL_AIM_STEP_PCT = 8
DUEL_BREAK_BASE_PCT = 22
DUEL_BREAK_STEP_PCT = 8

def _duel_stake_text(amount: int) -> str:
    n = int(amount or 0)
    return f"{_fmt_k(n)} {_ru_form(n, 'био-материал', 'био-материала', 'био-материалов')}"

def _duel_break_chance_from_bonus(opponent_bonus: int) -> int:
    bonus = max(0, int(opponent_bonus or 0))
    if bonus <= 0:
        return 0

    aim_step = max(1, int(DUEL_AIM_STEP_PCT))
    stacks = int(math.ceil(float(bonus) / float(aim_step)))
    chance = int(DUEL_BREAK_BASE_PCT + stacks * DUEL_BREAK_STEP_PCT)

    if chance < 0:
        chance = 0
    elif chance > 100:
        chance = 100

    return int(chance)

def _duel_accept_cb(invite_id: int, target_id: int) -> str:
    return f"{CB_DUEL_ACCEPT}:{int(invite_id)}:{int(target_id)}"

def _duel_decline_cb(invite_id: int, target_id: int) -> str:
    return f"{CB_DUEL_DECLINE}:{int(invite_id)}:{int(target_id)}"

def _duel_inv_cancel_cb(invite_id: int, challenger_id: int) -> str:
    return f"{CB_DUEL_INV_CANCEL}:{int(invite_id)}:{int(challenger_id)}"

def _duel_rematch_cb(duel_id: int, actor_id: int = 0) -> str:
    return f"{CB_DUEL_REMATCH}:{int(duel_id)}:{int(actor_id)}"

def _duel_random_cb(actor_id: int) -> str:
    return f"{CB_DUEL_RANDOM}:{int(actor_id)}"

def kb_duel_no_active(actor_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb("Случайная дуэль", callback_data=_duel_random_cb(int(actor_id)), style="primary")
    )
    return kb

def kb_duel_invite(invite_id: int, target_id: int, challenger_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        _ikb("🗡️ Принять", callback_data=_duel_accept_cb(int(invite_id), int(target_id)), style="success"),
        _ikb("🏳️ Отказать", callback_data=_duel_decline_cb(int(invite_id), int(target_id)), style="danger"),
    )
    kb.row(
        _ikb("✖️ Отменить дуэль", callback_data=_duel_inv_cancel_cb(int(invite_id), int(challenger_id)), style="danger")
    )
    return kb

def kb_duel_rematch(duel_row) -> Optional[InlineKeyboardMarkup]:
    if not duel_row:
        return None

    status = (duel_row["status"] or "").strip()
    if status not in ("finished", "draw"):
        return None

    duel_id = int(duel_row["duel_id"])
    allowed_id = int(duel_row["loser_id"] or 0) if status == "finished" else 0

    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb("⚔️ Реванш", callback_data=_duel_rematch_cb(int(duel_id), int(allowed_id)), style="primary")
    )
    return kb

def _duel_invite_text(chat_id: int, challenger_id: int, target_id: int, stake_amount: int = 0) -> str:
    with chat_name_context(int(chat_id)):
        target_tag = public_user_tag(int(target_id))
        challenger_tag = public_user_tag(int(challenger_id))

    lines = [
        f"⚔️ <b>{target_tag}</b>, минуточку внимания!",
        f"<b>{challenger_tag}</b> вызывает Вас на дуэль",
    ]
    if int(stake_amount or 0) > 0:
        lines.append(f"Ставка: 💊 {_duel_stake_text(int(stake_amount))}")
    lines.append("")
    lines.append('💬 Чтобы принять вызов, введите "<code>Био дуэль да</code>", или отменить "<code>Био дуэль нет</code>"')
    lines.append("На принятие решения у вас есть 5 минут")
    return "\n".join(lines)

def _duel_declined_text(chat_id: int, challenger_id: int, target_id: int) -> str:
    with chat_name_context(int(chat_id)):
        challenger_tag = public_user_tag(int(challenger_id))
        target_tag = public_user_tag(int(target_id))
    return f"🏳️ <b>{target_tag}</b> {_gender_pick(int(target_id), 'duel_refuse')} от дуэли с <b>{challenger_tag}</b>."

def _duel_invite_expired_text() -> str:
    return "📜 Никто из участников дуэли не проявили активности.\nДуэль отменена."

def _duel_started_text(chat_id: int, challenger_id: int, target_id: int, stake_amount: int, first_turn_id: int) -> str:
    with chat_name_context(int(chat_id)):
        target_tag = public_user_tag(int(target_id))
        challenger_tag = public_user_tag(int(challenger_id))
        first_tag = public_user_tag(int(first_turn_id))

    lines = [
        f"✅ <b>{target_tag}</b> {_gender_pick(int(target_id), 'duel_ready')} вызов <b>{challenger_tag}</b> на дуэль" + (
            f" со ставкой 💊 {_duel_stake_text(int(stake_amount))}" if int(stake_amount or 0) > 0 else ""
        ),
        'На время дуэли другие игроки могут делать свои ставки, команда "<code>Био ставка</code> [кол-во био-материалов] {кандидат}"',
        "",
        f"Право первого выстрела предоставляется <b>{first_tag}</b>",
        "На каждый выстрел у вас есть 5 минут",
        '💬 Произвести выстрел: "<code>Био выстрел</code>"',
    ]
    return "\n".join(lines)

def _duel_superseded_text(chat_id: int, challenger_id: int, target_id: int, accepted_challenger_id: int) -> str:
    with chat_name_context(int(chat_id)):
        challenger_tag = public_user_tag(int(challenger_id))
        target_tag = public_user_tag(int(target_id))
        accepted_tag = public_user_tag(int(accepted_challenger_id))

    return (
        f"📜 <b>{challenger_tag}</b>, смеем Вам сообщить!\n"
        f"<b>{target_tag}</b> принял вызов на дуэль <b>{accepted_tag}</b>.\n"
        "Вызовите на дуэль другого игрока или подождите, пока этот игрок завершит текущую дуэль."
    )

def _duel_inactive_text(chat_id: int, current_turn_user_id: int) -> str:
    with chat_name_context(int(chat_id)):
        cur_tag = public_user_tag(int(current_turn_user_id))
    return f"📜 <b>{cur_tag}</b> не {_gender_pick(int(current_turn_user_id), 'duel_timeout')} активности.\nДуэль отменена."

def _duel_refund_materials(user_id: int, amount: int):
    amt = int(amount or 0)
    if amt <= 0:
        return
    db_exec(
        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? WHERE user_id=?",
        (amt, int(user_id)),
        commit=True
    )

def _duel_take_materials(user_id: int, amount: int) -> bool:
    amt = int(amount or 0)
    if amt <= 0:
        return True

    row = db_one("SELECT COALESCE(all_bio_mater,0) AS m FROM labs WHERE user_id=?", (int(user_id),))
    have = int(row["m"] or 0) if row else 0
    if have < amt:
        return False

    db_exec(
        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)-? WHERE user_id=?",
        (amt, int(user_id)),
        commit=True
    )
    return True

def _duel_user_has_active_duel_in_chat(chat_id: int, user_id: int) -> bool:
    row = db_one(
        "SELECT 1 FROM duels "
        "WHERE chat_id=? AND status='active' AND (challenger_id=? OR target_id=?) "
        "LIMIT 1",
        (int(chat_id), int(user_id), int(user_id))
    )
    return row is not None

def _duel_user_has_outgoing_pending_invite_in_chat(chat_id: int, user_id: int) -> bool:
    row = db_one(
        "SELECT 1 FROM duel_invites "
        "WHERE chat_id=? AND status='pending' AND challenger_id=? "
        "LIMIT 1",
        (int(chat_id), int(user_id))
    )
    return row is not None

def _duel_user_has_any_pending_invite_in_chat(chat_id: int, user_id: int) -> bool:
    row = db_one(
        "SELECT 1 FROM duel_invites "
        "WHERE chat_id=? AND status='pending' AND (challenger_id=? OR target_id=?) "
        "LIMIT 1",
        (int(chat_id), int(user_id), int(user_id))
    )
    return row is not None

def _duel_random_candidate_ids(chat_id: int, actor_id: int) -> list[int]:
    rows = db_all(
        "SELECT cm.user_id, COALESCE(u.is_bot,0) AS is_bot "
        "FROM chat_members cm "
        "LEFT JOIN users u ON u.user_id=cm.user_id "
        "WHERE cm.chat_id=? AND cm.user_id<>? "
        "ORDER BY cm.user_id ASC",
        (int(chat_id), int(actor_id))
    ) or []

    out: list[int] = []
    for r in rows:
        uid = int(r["user_id"] or 0)
        if uid <= 0:
            continue
        if int(r["is_bot"] or 0) == 1:
            continue
        if _duel_user_has_active_duel_in_chat(int(chat_id), int(uid)):
            continue
        if _duel_user_has_any_pending_invite_in_chat(int(chat_id), int(uid)):
            continue
        out.append(int(uid))

    return out

def _duel_pick_random_target(chat_id: int, actor_id: int) -> int:
    pool = _duel_random_candidate_ids(int(chat_id), int(actor_id))
    if not pool:
        return 0
    return int(random.choice(pool))

def _duel_latest_pending_invite_for_target(chat_id: int, target_id: int):
    return db_one(
        "SELECT invite_id, chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id "
        "FROM duel_invites "
        "WHERE chat_id=? AND target_id=? AND status='pending' "
        "ORDER BY invite_id DESC LIMIT 1",
        (int(chat_id), int(target_id))
    )

def _duel_invite_by_id(invite_id: int):
    return db_one(
        "SELECT invite_id, chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id "
        "FROM duel_invites WHERE invite_id=? LIMIT 1",
        (int(invite_id),)
    )

def _duel_latest_outgoing_pending_invite(chat_id: int, challenger_id: int):
    return db_one(
        "SELECT invite_id, chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id "
        "FROM duel_invites "
        "WHERE chat_id=? AND challenger_id=? AND status='pending' "
        "ORDER BY invite_id DESC LIMIT 1",
        (int(chat_id), int(challenger_id))
    )

def _duel_invite_cancelled_text(chat_id: int, challenger_id: int, target_id: int, stake_amount: int = 0) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(challenger_id))
        ttag = public_user_tag(int(target_id))

    txt = f"✖️ <b>{ctag}</b> {_gender_pick(int(challenger_id), 'duel_cancel')} вызов на дуэль для <b>{ttag}</b>."
    if int(stake_amount or 0) > 0:
        txt += "\n💊 Ставка инициатора возвращена."
    return txt

def _duel_cancel_pending_invite(invite_row, actor_id: int, *, via_message=None, edit_existing: bool = True) -> tuple[bool, str]:
    if not invite_row:
        return False, "📑 Вызов на дуэль не найден."

    if (invite_row["status"] or "").strip() != "pending":
        return False, "📑 Этот вызов уже неактивен."

    challenger_id = int(invite_row["challenger_id"] or 0)
    if int(actor_id) != int(challenger_id):
        return False, "📑 Отменить вызов может только его инициатор."

    db_exec(
        "UPDATE duel_invites SET status='cancelled' WHERE invite_id=?",
        (int(invite_row["invite_id"]),),
        commit=True
    )
    _duel_refund_invite_stake(invite_row)

    txt = _duel_invite_cancelled_text(
        int(invite_row["chat_id"]),
        int(invite_row["challenger_id"]),
        int(invite_row["target_id"]),
        int(invite_row["stake_amount"] or 0)
    )

    if edit_existing:
        _duel_edit_invite_message(invite_row, txt, reply_markup=None)
    else:
        try:
            if via_message is not None:
                bot.reply_to(via_message, txt, parse_mode="HTML", disable_web_page_preview=True)
            else:
                bot.send_message(
                    int(invite_row["chat_id"]),
                    txt,
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
        except Exception:
            pass

    return True, "❎ Вызов на дуэль отменён."

def _duel_rematch_started_text(chat_id: int, challenger_id: int, target_id: int, stake_amount: int, first_turn_id: int) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(challenger_id))
        ttag = public_user_tag(int(target_id))
        ftag = public_user_tag(int(first_turn_id))

    lines = [
        f"⚔️ <b>{ctag}</b> и <b>{ttag}</b> начинают реванш" + (
            f" на ставку 💊 {_duel_stake_text(int(stake_amount))}" if int(stake_amount or 0) > 0 else ""
        ),
        "",
        f"Право первого выстрела предоставляется <b>{ftag}</b>",
        "На каждый выстрел у вас есть 5 минут",
        '💬 Произвести выстрел: "<code>Био выстрел</code>"',
    ]
    return "\n".join(lines)

def _duel_start_rematch_from_finished(duel_row, actor_id: int) -> tuple[bool, str]:
    if not duel_row:
        return False, "📑 Дуэль не найдена."

    status = (duel_row["status"] or "").strip()
    if status not in ("finished", "draw"):
        return False, "📑 Реванш доступен только после завершения дуэли."

    challenger_id = int(duel_row["challenger_id"] or 0)
    target_id = int(duel_row["target_id"] or 0)
    stake_amount = int(duel_row["stake_amount"] or 0)
    chat_id = int(duel_row["chat_id"] or 0)

    allowed = set()
    if status == "finished":
        loser_id = int(duel_row["loser_id"] or 0)
        allowed = {loser_id} if loser_id > 0 else set()
        if int(actor_id) not in allowed:
            return False, "📑 Реванш может начать только проигравший игрок."
    else:
        allowed = {challenger_id, target_id}
        if int(actor_id) not in allowed:
            return False, "📑 При ничьей реванш может начать только один из участников дуэли."

    if not is_lab_active(int(challenger_id)) or not is_lab_active(int(target_id)):
        return False, "📑 Один из участников ещё не создал лабораторию."

    if _duel_user_has_active_duel_in_chat(int(chat_id), int(challenger_id)) or _duel_user_has_outgoing_pending_invite_in_chat(int(chat_id), int(challenger_id)):
        return False, "📑 Один из участников уже занят другой дуэлью или ожидает ответа."
    if _duel_user_has_active_duel_in_chat(int(chat_id), int(target_id)) or _duel_user_has_outgoing_pending_invite_in_chat(int(chat_id), int(target_id)):
        return False, "📑 Один из участников уже занят другой дуэлью или ожидает ответа."

    if stake_amount > 0:
        if not _duel_take_materials(int(challenger_id), int(stake_amount)):
            return False, "📝 У одного из участников недостаточно био-материалов для реванша."
        if not _duel_take_materials(int(target_id), int(stake_amount)):
            _duel_refund_materials(int(challenger_id), int(stake_amount))
            return False, "📝 У одного из участников недостаточно био-материалов для реванша."

    now = int(now_ts())
    first_turn_id = random.choice([int(challenger_id), int(target_id)])

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute(
                "INSERT INTO duels("
                "invite_id, chat_id, challenger_id, target_id, stake_amount, "
                "started_at, next_action_until, current_turn_user_id, "
                "turns_done, challenger_aim_bonus, target_aim_bonus, "
                "status, winner_id, loser_id, msg_chat_id, msg_id, ended_at"
                ") VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    0,                                  # invite_id
                    int(chat_id),                       # chat_id
                    int(challenger_id),                 # challenger_id
                    int(target_id),                     # target_id
                    int(stake_amount),                  # stake_amount
                    int(now),                           # started_at
                    int(now + DUEL_TURN_TIMEOUT_SEC),   # next_action_until
                    int(first_turn_id),                 # current_turn_user_id
                    0,                                  # turns_done
                    0,                                  # challenger_aim_bonus
                    0,                                  # target_aim_bonus
                    "active",                           # status
                    0,                                  # winner_id
                    0,                                  # loser_id
                    int(duel_row["msg_chat_id"] or 0),  # msg_chat_id
                    int(duel_row["msg_id"] or 0),       # msg_id
                    0,                                  # ended_at
                )
            )
            new_duel_id = int(c.lastrowid)
            conn.commit()
        except Exception:
            conn.rollback()
            if stake_amount > 0:
                _duel_refund_materials(int(challenger_id), int(stake_amount))
                _duel_refund_materials(int(target_id), int(stake_amount))
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    fresh = _duel_by_id(int(new_duel_id))
    txt = _duel_rematch_started_text(
        int(chat_id),
        int(challenger_id),
        int(target_id),
        int(stake_amount),
        int(first_turn_id)
    )
    _duel_emit_state(fresh, txt, reply_markup=kb_duel_actions(fresh), edit_existing=True)
    return True, "✅ Реванш начался."

def _duel_mark_invite_message(invite_id: int, chat_id: int, msg_id: int):
    db_exec(
        "UPDATE duel_invites SET msg_chat_id=?, msg_id=? WHERE invite_id=?",
        (int(chat_id), int(msg_id), int(invite_id)),
        commit=True
    )

def _duel_edit_invite_message(invite_row, text: str, reply_markup=None):
    try:
        mch = int(invite_row["msg_chat_id"] or 0)
        mid = int(invite_row["msg_id"] or 0)
        if mch != 0 and mid != 0:
            limited_edit_message_text(
                text=text,
                chat_id=mch,
                msg_id=mid,
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=True
            )
    except Exception:
        pass

def _duel_edit_duel_message(duel_row, text: str, reply_markup=None):
    try:
        mch = int(duel_row["msg_chat_id"] or 0)
        mid = int(duel_row["msg_id"] or 0)
        if mch != 0 and mid != 0:
            limited_edit_message_text(
                text=text,
                chat_id=mch,
                msg_id=mid,
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=True
            )
    except Exception:
        pass

def _duel_refund_invite_stake(invite_row):
    amt = int(invite_row["stake_amount"] or 0)
    if amt > 0:
        _duel_refund_materials(int(invite_row["challenger_id"]), amt)

def _duel_refund_duel_stakes(duel_row):
    amt = int(duel_row["stake_amount"] or 0)
    if amt <= 0:
        return
    _duel_refund_materials(int(duel_row["challenger_id"]), amt)
    _duel_refund_materials(int(duel_row["target_id"]), amt)

def _duel_by_id(duel_id: int):
    return db_one(
        "SELECT duel_id, invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, current_turn_user_id, "
        "turns_done, challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, msg_chat_id, msg_id, ended_at "
        "FROM duels WHERE duel_id=? LIMIT 1",
        (int(duel_id),)
    )

def _duel_active_by_user_in_chat(chat_id: int, user_id: int):
    return db_one(
        "SELECT duel_id, invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, current_turn_user_id, "
        "turns_done, challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, msg_chat_id, msg_id, ended_at "
        "FROM duels "
        "WHERE chat_id=? AND status='active' AND (challenger_id=? OR target_id=?) "
        "ORDER BY duel_id DESC LIMIT 1",
        (int(chat_id), int(user_id), int(user_id))
    )

def _duel_set_message_ref(duel_id: int, chat_id: int, msg_id: int):
    db_exec(
        "UPDATE duels SET msg_chat_id=?, msg_id=? WHERE duel_id=?",
        (int(chat_id), int(msg_id), int(duel_id)),
        commit=True
    )

def _duel_started_text_from_row(duel_row) -> str:
    return _duel_started_text(
        int(duel_row["chat_id"]),
        int(duel_row["challenger_id"]),
        int(duel_row["target_id"]),
        int(duel_row["stake_amount"] or 0),
        int(duel_row["current_turn_user_id"] or 0),
    )

def _duel_actor_bonus_cols(duel_row, actor_id: int) -> tuple[str, str]:
    if int(actor_id) == int(duel_row["challenger_id"]):
        return "challenger_aim_bonus", "target_aim_bonus"
    return "target_aim_bonus", "challenger_aim_bonus"

def _duel_opponent_id(duel_row, actor_id: int) -> int:
    if int(actor_id) == int(duel_row["challenger_id"]):
        return int(duel_row["target_id"])
    return int(duel_row["challenger_id"])

def _duel_actor_bonus(duel_row, actor_id: int) -> int:
    if int(actor_id) == int(duel_row["challenger_id"]):
        return int(duel_row["challenger_aim_bonus"] or 0)
    return int(duel_row["target_aim_bonus"] or 0)

def _duel_action_cb(tag: str, duel_id: int, actor_id: int) -> str:
    return f"{str(tag)}:{int(duel_id)}:{int(actor_id)}"

def kb_duel_actions(duel_row) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    duel_id = int(duel_row["duel_id"])
    actor_id = int(duel_row["current_turn_user_id"] or 0)

    kb.row(
        _ikb("🔫 Выстрел", callback_data=_duel_action_cb(CB_DUEL_FIRE, duel_id, actor_id), style="success"),
        _ikb("👁️‍🗨️ Прицелиться", callback_data=_duel_action_cb(CB_DUEL_AIM, duel_id, actor_id)),
    )

    opponent_id = _duel_opponent_id(duel_row, actor_id)
    if _duel_actor_bonus(duel_row, opponent_id) > 0:
        kb.row(
            _ikb("🪃 Сбить прицел", callback_data=_duel_action_cb(CB_DUEL_BREAK_AIM, duel_id, actor_id))
        )

    if int(duel_row["turns_done"] or 0) == 0:
        kb.row(
            _ikb(
                "✖️ Отменить дуэль",
                callback_data=_duel_action_cb(CB_DUEL_CANCEL, duel_id, int(duel_row["challenger_id"])),
                style="danger"
            )
        )

    kb.row(
        _ikb("🏳️ Сдаться", callback_data=_duel_action_cb(CB_DUEL_SURRENDER, duel_id, actor_id), style="danger")
    )
    return kb

def _duel_emit_state(duel_row, text: str, reply_markup=None, *, via_message=None, edit_existing: bool = True):
    if edit_existing:
        mch = int(duel_row["msg_chat_id"] or 0)
        mid = int(duel_row["msg_id"] or 0)
        if mch != 0 and mid != 0:
            _duel_edit_duel_message(duel_row, text, reply_markup=reply_markup)
            return

    if via_message is not None:
        sent = bot.reply_to(
            via_message,
            text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=reply_markup
        )
    else:
        sent = bot.send_message(
            int(duel_row["chat_id"]),
            text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=reply_markup
        )

    try:
        _duel_set_message_ref(int(duel_row["duel_id"]), int(sent.chat.id), int(sent.message_id))
    except Exception:
        pass

def _duel_win_extra_line(chat_id: int, winner_id: int, stake_amount: int) -> str:
    amt = int(stake_amount or 0)
    if amt <= 0:
        return ""
    with chat_name_context(int(chat_id)):
        wtag = public_user_tag(int(winner_id))
    return f"\nПобедитель <b>{wtag}</b> получает на свой счёт +{_fmt_k(amt)} 💊"

def _duel_hit_text(chat_id: int, winner_id: int, loser_id: int, stake_amount: int) -> str:
    with chat_name_context(int(chat_id)):
        wtag = public_user_tag(int(winner_id))
        ltag = public_user_tag(int(loser_id))
    return (
        f"💀🔫 Попадание!\n"
        f"<b>{wtag}</b> {_gender_pick(int(winner_id), 'duel_hit')} в <b>{ltag}</b>"
        f"{_duel_win_extra_line(int(chat_id), int(winner_id), int(stake_amount))}"
    )

def _duel_miss_text(chat_id: int, actor_id: int, next_id: int) -> str:
    with chat_name_context(int(chat_id)):
        atag = public_user_tag(int(actor_id))
        ntag = public_user_tag(int(next_id))
    return (
        f"🔫 <b>{atag}</b> {_gender_pick(int(actor_id), 'duel_miss')}\n"
        f"Ход <b>{ntag}</b>:"
    )

def _duel_aim_text(chat_id: int, actor_id: int, next_id: int, multiplier: int) -> str:
    with chat_name_context(int(chat_id)):
        atag = public_user_tag(int(actor_id))
        ntag = public_user_tag(int(next_id))
    return (
        f"👁️‍🗨️ <b>{atag}</b> {_gender_pick(int(actor_id), 'duel_aim')} (×{int(multiplier)})\n"
        f"Ход <b>{ntag}</b>:"
    )

def _duel_break_aim_text(chat_id: int, actor_id: int, next_id: int) -> str:
    with chat_name_context(int(chat_id)):
        atag = public_user_tag(int(actor_id))
        ntag = public_user_tag(int(next_id))
    action_text = h(pick_duel_misalign_text(int(actor_id)))
    return (
        f"🪃 <b>{atag}</b> {action_text} {_gender_pick(int(actor_id), 'duel_break_tail')} <b>{ntag}</b>.\n"
        f"Ход <b>{ntag}</b>:"
    )

def _duel_break_aim_fail_text(chat_id: int, actor_id: int, next_id: int) -> str:
    with chat_name_context(int(chat_id)):
        atag = public_user_tag(int(actor_id))
        ntag = public_user_tag(int(next_id))
    return (
        f"🪃 <b>{atag}</b> {_gender_pick(int(actor_id), 'duel_break_fail')} <b>{ntag}</b>, {_gender_pick(int(actor_id), 'duel_break_fail_2')}.\n"
        f"Ход <b>{ntag}</b>:"
    )

def _duel_surrender_text(chat_id: int, winner_id: int, loser_id: int, stake_amount: int) -> str:
    with chat_name_context(int(chat_id)):
        wtag = public_user_tag(int(winner_id))
        ltag = public_user_tag(int(loser_id))
    return (
        f"🏳️ <b>{ltag}</b> {_gender_pick(int(loser_id), 'duel_surrender')}.\n"
        f"Победитель дуэли — <b>{wtag}</b>"
        f"{_duel_win_extra_line(int(chat_id), int(winner_id), int(stake_amount))}"
    )

def _duel_cancelled_text(chat_id: int, challenger_id: int, target_id: int, stake_amount: int) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(challenger_id))
        ttag = public_user_tag(int(target_id))

    txt = f"✖️ <b>{ctag}</b> {_gender_pick(int(challenger_id), 'duel_cancel')} дуэль с <b>{ttag}</b>."
    if int(stake_amount or 0) > 0:
        txt += "\n💊 Ставки дуэлянтов возвращены."
    return txt

def _duel_cancel_before_moves(duel_row, actor_id: int, *, via_message=None, edit_existing: bool = True) -> tuple[bool, str]:
    if not duel_row:
        return False, "📑 Дуэль не найдена."

    if (duel_row["status"] or "").strip() != "active":
        return False, "📑 Эта дуэль уже завершена."

    challenger_id = int(duel_row["challenger_id"] or 0)
    target_id = int(duel_row["target_id"] or 0)
    stake_amount = int(duel_row["stake_amount"] or 0)
    duel_id = int(duel_row["duel_id"] or 0)

    if int(actor_id) != int(challenger_id):
        return False, "📑 Отменить дуэль до начала ходов может только её инициатор."

    if int(duel_row["turns_done"] or 0) != 0:
        return False, "📑 Дуэль уже началась. Отменить её больше нельзя."

    now = int(now_ts())

    db_exec(
        "UPDATE duels SET status='cancelled', ended_at=?, next_action_until=0 WHERE duel_id=?",
        (int(now), int(duel_id)),
        commit=True
    )

    _duel_refund_duel_stakes(duel_row)
    _duel_mark_bets_refunded(int(duel_id))

    fresh = _duel_by_id(int(duel_id)) or duel_row
    txt = _duel_cancelled_text(
        int(duel_row["chat_id"]),
        int(challenger_id),
        int(target_id),
        int(stake_amount)
    )
    _duel_emit_state(fresh, txt, reply_markup=None, via_message=via_message, edit_existing=edit_existing)
    return True, "❎ Дуэль отменена."

def _duel_draw_text(chat_id: int, challenger_id: int, target_id: int) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(challenger_id))
        ttag = public_user_tag(int(target_id))
    return (
        "Ход завершён."
        f"🤝 <b>{ctag}</b> и <b>{ttag}</b> не смогли определить победителя.\n"
        f"Ничья."
    )

def _duel_stats_ensure(user_id: int):
    db_exec("INSERT OR IGNORE INTO duel_stats(user_id) VALUES (?)", (int(user_id),), commit=True)

def _duel_stats_add_win(user_id: int, stake_amount: int):
    _duel_stats_ensure(int(user_id))
    row = db_one(
        "SELECT wins, draws, losses, max_win_materials, max_lose_materials, win_streak, best_win_streak "
        "FROM duel_stats WHERE user_id=?",
        (int(user_id),)
    )
    cur_streak = int(row["win_streak"] or 0) if row else 0
    best_streak = int(row["best_win_streak"] or 0) if row else 0
    max_win = int(row["max_win_materials"] or 0) if row else 0

    new_streak = cur_streak + 1
    new_best = max(best_streak, new_streak)
    new_max_win = max(max_win, int(stake_amount or 0))

    db_exec(
        "UPDATE duel_stats SET wins=COALESCE(wins,0)+1, win_streak=?, best_win_streak=?, max_win_materials=? WHERE user_id=?",
        (int(new_streak), int(new_best), int(new_max_win), int(user_id)),
        commit=True
    )

def _duel_stats_add_loss(user_id: int, stake_amount: int):
    _duel_stats_ensure(int(user_id))
    row = db_one(
        "SELECT max_lose_materials FROM duel_stats WHERE user_id=?",
        (int(user_id),)
    )
    max_lose = int(row["max_lose_materials"] or 0) if row else 0
    new_max_lose = max(max_lose, int(stake_amount or 0))

    db_exec(
        "UPDATE duel_stats SET losses=COALESCE(losses,0)+1, win_streak=0, max_lose_materials=? WHERE user_id=?",
        (int(new_max_lose), int(user_id)),
        commit=True
    )

def _duel_stats_add_draw(user_id: int):
    _duel_stats_ensure(int(user_id))
    db_exec(
        "UPDATE duel_stats SET draws=COALESCE(draws,0)+1 WHERE user_id=?",
        (int(user_id),),
        commit=True
    )

def _duel_finish_victory(duel_row, winner_id: int, loser_id: int, text: str, *, via_message=None, edit_existing: bool = True):
    duel_id = int(duel_row["duel_id"])
    stake_amount = int(duel_row["stake_amount"] or 0)
    now = int(now_ts())

    if stake_amount > 0:
        db_exec(
            "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? WHERE user_id=?",
            (int(stake_amount * 2), int(winner_id)),
            commit=True
        )

    db_exec(
        "UPDATE duels SET status='finished', winner_id=?, loser_id=?, ended_at=?, next_action_until=0 WHERE duel_id=?",
        (int(winner_id), int(loser_id), int(now), int(duel_id)),
        commit=True
    )

    _duel_stats_add_win(int(winner_id), int(stake_amount))
    _duel_stats_add_loss(int(loser_id), int(stake_amount))

    fresh = _duel_by_id(int(duel_id)) or duel_row
    _duel_emit_state(
        fresh,
        text,
        reply_markup=kb_duel_rematch(fresh),
        via_message=via_message,
        edit_existing=edit_existing
    )

    try:
        _duel_settle_bets_victory(fresh, int(winner_id))
    except Exception as e:
        send_error_report("_duel_settle_bets_victory", e)

def _duel_finish_draw(duel_row, *, via_message=None, edit_existing: bool = True):
    duel_id = int(duel_row["duel_id"])
    now = int(now_ts())

    db_exec(
        "UPDATE duels SET status='draw', ended_at=?, next_action_until=0 WHERE duel_id=?",
        (int(now), int(duel_id)),
        commit=True
    )

    _duel_refund_duel_stakes(duel_row)
    _duel_mark_bets_refunded(int(duel_id))
    _duel_stats_add_draw(int(duel_row["challenger_id"]))
    _duel_stats_add_draw(int(duel_row["target_id"]))

    fresh = _duel_by_id(int(duel_id)) or duel_row
    txt = _duel_draw_text(
        int(duel_row["chat_id"]),
        int(duel_row["challenger_id"]),
        int(duel_row["target_id"])
    )
    _duel_emit_state(
        fresh,
        txt,
        reply_markup=kb_duel_rematch(fresh),
        via_message=via_message,
        edit_existing=edit_existing
    )

def _duel_finish_pass_turn(
    duel_row,
    *,
    actor_id: int,
    challenger_bonus: int,
    target_bonus: int,
    text: str,
    via_message=None,
    edit_existing: bool = True
):
    duel_id = int(duel_row["duel_id"])
    turns_done = int(duel_row["turns_done"] or 0) + 1

    if turns_done >= DUEL_MAX_TURNS:
        db_exec(
            "UPDATE duels SET turns_done=?, challenger_aim_bonus=?, target_aim_bonus=? WHERE duel_id=?",
            (int(turns_done), int(challenger_bonus), int(target_bonus), int(duel_id)),
            commit=True
        )
        fresh = _duel_by_id(int(duel_id)) or duel_row
        _duel_finish_draw(fresh, via_message=via_message, edit_existing=edit_existing)
        return

    next_id = _duel_opponent_id(duel_row, int(actor_id))
    db_exec(
        "UPDATE duels SET current_turn_user_id=?, next_action_until=?, turns_done=?, challenger_aim_bonus=?, target_aim_bonus=? WHERE duel_id=?",
        (
            int(next_id),
            int(now_ts() + DUEL_TURN_TIMEOUT_SEC),
            int(turns_done),
            int(challenger_bonus),
            int(target_bonus),
            int(duel_id),
        ),
        commit=True
    )

    fresh = _duel_by_id(int(duel_id)) or duel_row
    _duel_emit_state(
        fresh,
        text,
        reply_markup=kb_duel_actions(fresh),
        via_message=via_message,
        edit_existing=edit_existing
    )

def _duel_perform_action(duel_row, actor_id: int, action: str, *, via_message=None, edit_existing: bool = True) -> tuple[bool, str]:
    if not duel_row:
        return False, "📑 Дуэль не найдена."
    if (duel_row["status"] or "").strip() != "active":
        return False, "📑 Эта дуэль уже завершена."

    current_turn = int(duel_row["current_turn_user_id"] or 0)
    if int(actor_id) != current_turn:
        return False, "📑 Сейчас не ваш ход."

    challenger_id = int(duel_row["challenger_id"])
    target_id = int(duel_row["target_id"])
    stake_amount = int(duel_row["stake_amount"] or 0)

    actor_bonus_col, opponent_bonus_col = _duel_actor_bonus_cols(duel_row, int(actor_id))
    opponent_id = _duel_opponent_id(duel_row, int(actor_id))

    challenger_bonus = int(duel_row["challenger_aim_bonus"] or 0)
    target_bonus = int(duel_row["target_aim_bonus"] or 0)

    actor_bonus = challenger_bonus if actor_bonus_col == "challenger_aim_bonus" else target_bonus
    opponent_bonus = challenger_bonus if opponent_bonus_col == "challenger_aim_bonus" else target_bonus

    if action == "fire":
        hit_chance = max(0, min(100, DUEL_BASE_HIT_PCT + int(actor_bonus)))
        if random.randint(1, 100) <= int(hit_chance):
            txt = _duel_hit_text(int(duel_row["chat_id"]), int(actor_id), int(opponent_id), int(stake_amount))
            _duel_finish_victory(
                duel_row,
                int(actor_id),
                int(opponent_id),
                txt,
                via_message=via_message,
                edit_existing=edit_existing
            )
            return True, ""

        txt = _duel_miss_text(int(duel_row["chat_id"]), int(actor_id), int(opponent_id))
        _duel_finish_pass_turn(
            duel_row,
            actor_id=int(actor_id),
            challenger_bonus=int(challenger_bonus),
            target_bonus=int(target_bonus),
            text=txt,
            via_message=via_message,
            edit_existing=edit_existing
        )
        return True, ""

    if action == "aim":
        actor_bonus += DUEL_AIM_STEP_PCT
        multiplier = max(1, int(actor_bonus // DUEL_AIM_STEP_PCT))

        if actor_bonus_col == "challenger_aim_bonus":
            challenger_bonus = int(actor_bonus)
        else:
            target_bonus = int(actor_bonus)

        txt = _duel_aim_text(int(duel_row["chat_id"]), int(actor_id), int(opponent_id), int(multiplier))
        _duel_finish_pass_turn(
            duel_row,
            actor_id=int(actor_id),
            challenger_bonus=int(challenger_bonus),
            target_bonus=int(target_bonus),
            text=txt,
            via_message=via_message,
            edit_existing=edit_existing
        )
        return True, ""

    if action == "break":
        if int(opponent_bonus) <= 0:
            return False, "📑 У соперника нет активного прицела."

        break_chance = _duel_break_chance_from_bonus(int(opponent_bonus))

        if random.randint(1, 100) <= int(break_chance):
            if opponent_bonus_col == "challenger_aim_bonus":
                challenger_bonus = 0
            else:
                target_bonus = 0

            txt = _duel_break_aim_text(int(duel_row["chat_id"]), int(actor_id), int(opponent_id))
        else:
            txt = _duel_break_aim_fail_text(int(duel_row["chat_id"]), int(actor_id), int(opponent_id))

        _duel_finish_pass_turn(
            duel_row,
            actor_id=int(actor_id),
            challenger_bonus=int(challenger_bonus),
            target_bonus=int(target_bonus),
            text=txt,
            via_message=via_message,
            edit_existing=edit_existing
        )
        return True, ""

    if action == "surrender":
        txt = _duel_surrender_text(int(duel_row["chat_id"]), int(opponent_id), int(actor_id), int(stake_amount))
        _duel_finish_victory(
            duel_row,
            int(opponent_id),
            int(actor_id),
            txt,
            via_message=via_message,
            edit_existing=edit_existing
        )
        return True, ""

    return False, "📑 Неизвестное действие дуэли."

def _duel_active_rows_in_chat(chat_id: int):
    return db_all(
        "SELECT duel_id, invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, "
        "current_turn_user_id, turns_done, challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, "
        "msg_chat_id, msg_id, ended_at "
        "FROM duels "
        "WHERE chat_id=? AND status='active' "
        "ORDER BY duel_id ASC",
        (int(chat_id),)
    ) or []

def _duel_find_active_by_candidate(chat_id: int, candidate_id: int):
    return db_one(
        "SELECT duel_id, invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, "
        "current_turn_user_id, turns_done, challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, "
        "msg_chat_id, msg_id, ended_at "
        "FROM duels "
        "WHERE chat_id=? AND status='active' AND (challenger_id=? OR target_id=?) "
        "ORDER BY duel_id DESC LIMIT 1",
        (int(chat_id), int(candidate_id), int(candidate_id))
    )

def _duel_active_bets(duel_id: int):
    return db_all(
        "SELECT bet_id, duel_id, chat_id, bettor_id, candidate_id, amount, created_at, status "
        "FROM duel_bets WHERE duel_id=? AND status='active' ORDER BY bet_id ASC",
        (int(duel_id),)
    ) or []

def _duel_bet_by_user(duel_id: int, bettor_id: int):
    return db_one(
        "SELECT bet_id, duel_id, chat_id, bettor_id, candidate_id, amount, created_at, status "
        "FROM duel_bets WHERE duel_id=? AND bettor_id=? AND status='active' LIMIT 1",
        (int(duel_id), int(bettor_id))
    )

def _duel_bettors_count(duel_id: int, candidate_id: int) -> int:
    row = db_one(
        "SELECT COUNT(*) AS c FROM duel_bets WHERE duel_id=? AND candidate_id=? AND status='active'",
        (int(duel_id), int(candidate_id))
    )
    return int(row["c"] or 0) if row else 0

def _duel_bet_count_text(cnt: int, highlighted: bool) -> str:
    s = str(int(cnt))
    return f"<u>{s}</u>" if highlighted else s

def render_duel_bets_text(chat_id: int, viewer_id: int, chat_title: str) -> str:
    rows = _duel_active_rows_in_chat(int(chat_id))
    title = (chat_title or "").strip() or f"Чат {int(chat_id)}"

    lines = [
        f"💰 Текущие дуэли чата <b>{h(title)}</b>",
        "№|имя1|став1|имя2|став2|ваша ставка",
    ]

    if not rows:
        lines.append("Активных дуэлей нет.")
        return "\n".join(lines)

    with chat_name_context(int(chat_id)):
        for i, row in enumerate(rows, 1):
            duel_id = int(row["duel_id"])
            c_id = int(row["challenger_id"])
            t_id = int(row["target_id"])

            my_bet = _duel_bet_by_user(int(duel_id), int(viewer_id))
            my_candidate = int(my_bet["candidate_id"]) if my_bet else 0
            my_amount = int(my_bet["amount"] or 0) if my_bet else 0

            c_cnt = _duel_bettors_count(int(duel_id), int(c_id))
            t_cnt = _duel_bettors_count(int(duel_id), int(t_id))

            c_tag = public_user_tag(int(c_id))
            t_tag = public_user_tag(int(t_id))

            right = f" | +{_fmt_k(int(my_amount))}💊" if my_bet else ""
            lines.append(
                f"{i}. <b>{c_tag}</b> ({_duel_bet_count_text(c_cnt, my_candidate == c_id)}) | "
                f"<b>{t_tag}</b> ({_duel_bet_count_text(t_cnt, my_candidate == t_id)}){right}"
            )

    return "\n".join(lines)

def _duel_parse_bet_args(message, parsed: Parsed):
    tail = (parsed.args or "").strip()
    parts = tail.split(None, 1)

    if not parts or not parts[0].isdigit():
        return 0, None, None, "📑 Укажите количество био-материалов и пользователя."

    amount = int(parts[0])
    if amount <= 0:
        return 0, None, None, "📑 Ставка должна быть больше нуля."

    target_tail = parts[1].strip() if len(parts) > 1 else ""
    fake = Parsed(
        raw=parsed.raw,
        has_prefix_char=parsed.has_prefix_char,
        prefix_char=parsed.prefix_char,
        cmd=parsed.cmd,
        args=target_tail
    )
    target_id, target_user_obj = resolve_target_from_reply_or_args(message, fake)
    if target_id is None:
        return 0, None, None, "📑 Укажите пользователя через @username, ссылку, user_id или reply."

    return int(amount), int(target_id), target_user_obj, ""

def _duel_place_bet(chat_id: int, bettor_id: int, candidate_id: int, amount: int):
    duel_row = _duel_find_active_by_candidate(int(chat_id), int(candidate_id))
    if not duel_row:
        return False, "📑 В этом чате у указанного игрока сейчас нет активной дуэли.", None

    duel_id = int(duel_row["duel_id"])
    challenger_id = int(duel_row["challenger_id"])
    target_id = int(duel_row["target_id"])

    if int(bettor_id) in (int(challenger_id), int(target_id)):
        return False, "📑 Участники дуэли не могут ставить на себя и на своего соперника.", duel_row

    have_row = db_one("SELECT COALESCE(all_bio_mater,0) AS m FROM labs WHERE user_id=?", (int(bettor_id),))
    have = int(have_row["m"] or 0) if have_row else 0
    if have < int(amount):
        return False, "📝 У вас нет столько био-материалов для ставки.", duel_row

    old_bet = _duel_bet_by_user(int(duel_id), int(bettor_id))
    if old_bet:
        return False, "📑 Вы уже сделали ставку на эту дуэль.", duel_row

    db_exec(
        "INSERT INTO duel_bets(duel_id, chat_id, bettor_id, candidate_id, amount, created_at, status) "
        "VALUES (?,?,?,?,?,?, 'active')",
        (int(duel_id), int(chat_id), int(bettor_id), int(candidate_id), int(amount), int(now_ts())),
        commit=True
    )

    return True, "", duel_row

def _duel_mark_bets_refunded(duel_id: int):
    db_exec(
        "UPDATE duel_bets SET status='refunded' WHERE duel_id=? AND status='active'",
        (int(duel_id),),
        commit=True
    )

def _duel_post_winning_bets_summary(chat_id: int, payouts: list[tuple[int, int]]):
    if not payouts:
        return

    with chat_name_context(int(chat_id)):
        lines = ["📜 Игроки, поставившие на победителя:"]
        for bettor_id, payout in payouts:
            btag = public_user_tag(int(bettor_id))
            lines.append(f"<b>{btag}</b> +{_fmt_k(int(payout))}💊")

    try:
        bot.send_message(
            int(chat_id),
            "\n".join(lines),
            parse_mode="HTML",
            disable_web_page_preview=True
        )
    except Exception:
        pass

def _duel_bet_success_notice_text(chat_id: int, candidate_id: int, payout: int) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(candidate_id))
    return (
        f"💵 УСПЕХ! Ставка на игрока <b>{ctag}</b> сыграла.\n"
        f"+{_fmt_k(int(payout))}💊"
    )

def _duel_bet_fail_notice_text(chat_id: int, candidate_id: int) -> str:
    with chat_name_context(int(chat_id)):
        ctag = public_user_tag(int(candidate_id))
    return (
        f"💸 Сожалеем, но <b>{ctag}</b> проиграл. Ваша ставка сгорела."
    )

def _duel_send_bet_result_notice(chat_id: int, bettor_id: int, candidate_id: int, *, won: bool, payout: int = 0):
    text = (
        _duel_bet_success_notice_text(int(chat_id), int(candidate_id), int(payout))
        if won else
        _duel_bet_fail_notice_text(int(chat_id), int(candidate_id))
    )
    try:
        send_user_notification(int(bettor_id), text)
    except Exception:
        pass

def _duel_rating_pct_value(wins: int, draws: int, losses: int) -> float:
    wins = int(wins or 0)
    draws = int(draws or 0)
    losses = int(losses or 0)
    total = wins + draws + losses
    if total <= 0:
        return 0.0
    return ((wins + draws) / total) * 100.0

def _duel_streak_label(streak: int) -> str:
    s = int(streak or 0)
    if s >= 10:
        return "(Serial killer)"
    if s == 9:
        return "(Unstoppable)"
    if s == 8:
        return "(Monster Kill)"
    if s == 7:
        return "(Wicked Sick)"
    if s == 6:
        return "(Ultra Kill)"
    if s == 5:
        return "(Rampage)"
    if s == 4:
        return "(Overkill)"
    if s == 3:
        return "(Triple Kill)"
    if s == 2:
        return "(Double Kill)"
    return ""

def _duel_current_win_streak_from_history(history: list[str]) -> int:
    streak = 0
    for mark in reversed(list(history or [])):
        m = str(mark or "").upper()
        if m == "W":
            streak += 1
            continue
        if m == "D":
            continue
        break
    return int(streak)

def _duel_collect_chat_stats(chat_id: int) -> list[dict]:
    rows = db_all(
        "SELECT duel_id, challenger_id, target_id, stake_amount, status, winner_id, loser_id, ended_at "
        "FROM duels "
        "WHERE chat_id=? AND status IN ('finished','draw') "
        "ORDER BY COALESCE(ended_at,0) ASC, duel_id ASC",
        (int(chat_id),)
    ) or []

    stats: dict[int, dict] = {}

    def _ensure(uid: int) -> dict:
        uid = int(uid)
        if uid not in stats:
            stats[uid] = {
                "user_id": uid,
                "wins": 0,
                "draws": 0,
                "losses": 0,
                "max_win_materials": 0,
                "max_lose_materials": 0,
                "history": [],
            }
        return stats[uid]

    for r in rows:
        challenger_id = int(r["challenger_id"] or 0)
        target_id = int(r["target_id"] or 0)
        stake_amount = int(r["stake_amount"] or 0)
        status = (r["status"] or "").strip()

        if challenger_id > 0:
            _ensure(int(challenger_id))
        if target_id > 0:
            _ensure(int(target_id))

        if status == "finished":
            winner_id = int(r["winner_id"] or 0)
            loser_id = int(r["loser_id"] or 0)

            if winner_id > 0:
                w = _ensure(int(winner_id))
                w["wins"] = int(w["wins"]) + 1
                w["max_win_materials"] = max(int(w["max_win_materials"]), int(stake_amount))
                w["history"].append("W")

            if loser_id > 0:
                l = _ensure(int(loser_id))
                l["losses"] = int(l["losses"]) + 1
                l["max_lose_materials"] = max(int(l["max_lose_materials"]), int(stake_amount))
                l["history"].append("L")

        elif status == "draw":
            for uid in (challenger_id, target_id):
                if int(uid) <= 0:
                    continue
                d = _ensure(int(uid))
                d["draws"] = int(d["draws"]) + 1
                d["history"].append("D")

    out = list(stats.values())
    for row in out:
        row["pct"] = float(_duel_rating_pct_value(
            int(row["wins"]),
            int(row["draws"]),
            int(row["losses"])
        ))
        row["streak"] = int(_duel_current_win_streak_from_history(row["history"]))

    out.sort(
        key=lambda x: (
            -int(x["wins"]),
            -float(x["pct"]),
            int(x["losses"]),
            int(x["user_id"]),
        )
    )
    return out

def render_duel_stats_text(chat_id: int, chat_title: str) -> str:
    title = (chat_title or "").strip() or f"Чат {int(chat_id)}"
    rows = _duel_collect_chat_stats(int(chat_id))

    lines = [
        f"⚔️ Рейтинг дуэлянтов беседы <b>{h(title)}</b>",
        "№|имя|в|н|п|выигр/проигр",
    ]

    if not rows:
        lines.append("Нет данных.")
        return "\n".join(lines)

    with chat_name_context(int(chat_id)):
        for i, row in enumerate(rows, 1):
            tag = public_user_tag(int(row["user_id"]))
            pct_text = _fmt_pct_text(float(row["pct"]))
            extra = _duel_streak_label(int(row["streak"]))
            extra = f" {extra}" if extra else ""

            lines.append(
                f"{i}. <b>{tag}</b>: "
                f"<b>{int(row['wins'])}</b> | "
                f"<b>{int(row['draws'])}</b> | "
                f"<b>{int(row['losses'])}</b> | "
                f"({pct_text}) | "
                f"💊 {_fmt_k(int(row['max_win_materials']))} / {_fmt_k(int(row['max_lose_materials']))} {extra}"
            )

    return "\n".join(lines)

def _duel_settle_bets_victory(duel_row, winner_id: int):
    duel_id = int(duel_row["duel_id"])
    chat_id = int(duel_row["chat_id"])

    rows = _duel_active_bets(int(duel_id))
    if not rows:
        return

    winners = []
    losers = []
    for r in rows:
        if int(r["candidate_id"]) == int(winner_id):
            winners.append(r)
        else:
            losers.append(r)

    total_lost = sum(int(r["amount"] or 0) for r in losers)
    share = (int(total_lost) // len(winners)) if winners else 0

    payouts_for_summary: list[tuple[int, int]] = []
    winner_notices: list[tuple[int, int, int]] = []
    loser_notices: list[tuple[int, int]] = []

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            for r in losers:
                bet_id = int(r["bet_id"])
                bettor_id = int(r["bettor_id"])
                candidate_id = int(r["candidate_id"])
                amount = int(r["amount"] or 0)

                c.execute(
                    "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)-? WHERE user_id=?",
                    (int(amount), int(bettor_id))
                )
                c.execute("UPDATE duel_bets SET status='lost' WHERE bet_id=?", (int(bet_id),))
                loser_notices.append((int(bettor_id), int(candidate_id)))

            for r in winners:
                bet_id = int(r["bet_id"])
                bettor_id = int(r["bettor_id"])
                candidate_id = int(r["candidate_id"])
                amount = int(r["amount"] or 0)

                own_bonus = int(amount * 0.1)
                payout = int(share + own_bonus)

                c.execute(
                    "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? WHERE user_id=?",
                    (int(payout), int(bettor_id))
                )
                c.execute("UPDATE duel_bets SET status='paid' WHERE bet_id=?", (int(bet_id),))

                payouts_for_summary.append((int(bettor_id), int(payout)))
                winner_notices.append((int(bettor_id), int(candidate_id), int(payout)))

            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    _duel_post_winning_bets_summary(int(chat_id), payouts_for_summary)

    for bettor_id, candidate_id, payout in winner_notices:
        _duel_send_bet_result_notice(
            int(chat_id),
            int(bettor_id),
            int(candidate_id),
            won=True,
            payout=int(payout)
        )

    for bettor_id, candidate_id in loser_notices:
        _duel_send_bet_result_notice(
            int(chat_id),
            int(bettor_id),
            int(candidate_id),
            won=False,
            payout=0
        )

def _duel_parse_call_args(message, parsed: Parsed, with_stake: bool):
    chat_id = int(message.chat.id)
    stake_amount = 0

    if with_stake:
        tail = (parsed.args or "").strip()
        parts = tail.split(None, 1)
        if not parts or not parts[0].isdigit():
            return None, None, 0, "📑 Укажите ставку и пользователя."
        stake_amount = int(parts[0])
        if stake_amount <= 0:
            return None, None, 0, "📑 Ставка должна быть больше нуля."
        target_tail = parts[1].strip() if len(parts) > 1 else ""

        fake = Parsed(
            raw=parsed.raw,
            has_prefix_char=parsed.has_prefix_char,
            prefix_char=parsed.prefix_char,
            cmd=parsed.cmd,
            args=target_tail
        )
        target_id, target_user_obj = resolve_target_from_reply_or_args(message, fake)
        if target_id is None:
            return None, None, 0, "📑 Укажите пользователя через @username, ссылку, user_id или reply."
        return int(target_id), target_user_obj, int(stake_amount), ""

    target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
    if target_id is None:
        return None, None, 0, "📑 Укажите пользователя через @username, ссылку, user_id или reply."
    return int(target_id), target_user_obj, 0, ""

def _duel_create_invite(chat_id: int, challenger_id: int, target_id: int, stake_amount: int):
    now = int(now_ts())
    expires_at = int(now + DUEL_INVITE_TIMEOUT_SEC)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            c.execute(
                "INSERT INTO duel_invites(chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id) "
                "VALUES (?,?,?,?,?,?, 'pending', 0, 0)",
                (int(chat_id), int(challenger_id), int(target_id), int(stake_amount), int(now), int(expires_at))
            )
            invite_id = int(c.lastrowid)
            conn.commit()
            return invite_id
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

def _duel_cancel_other_invites_for_target(chat_id: int, target_id: int, accepted_invite_id: int, accepted_challenger_id: int):
    rows = db_all(
        "SELECT invite_id, chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id "
        "FROM duel_invites "
        "WHERE chat_id=? AND target_id=? AND status='pending' AND invite_id<>? "
        "ORDER BY invite_id ASC",
        (int(chat_id), int(target_id), int(accepted_invite_id))
    ) or []

    for r in rows:
        db_exec("UPDATE duel_invites SET status='superseded' WHERE invite_id=?", (int(r["invite_id"]),), commit=True)
        _duel_refund_invite_stake(r)
        txt = _duel_superseded_text(int(chat_id), int(r["challenger_id"]), int(target_id), int(accepted_challenger_id))
        _duel_edit_invite_message(r, txt)

def _duel_accept_invite(invite_id: int, actor_id: int, *, edit_invite_message: bool = True):
    inv = _duel_invite_by_id(int(invite_id))
    if not inv:
        return False, "📑 Вызов на дуэль не найден."

    if (inv["status"] or "").strip() != "pending":
        return False, "📑 Этот вызов уже неактивен."

    if int(inv["target_id"]) != int(actor_id):
        return False, "📑 Этот вызов адресован не вам."

    chat_id = int(inv["chat_id"])
    challenger_id = int(inv["challenger_id"])
    target_id = int(inv["target_id"])
    stake_amount = int(inv["stake_amount"] or 0)

    if _duel_user_has_active_duel_in_chat(chat_id, challenger_id):
        return False, "📑 Вызвавший игрок уже участвует в другой дуэли в этом чате."
    if _duel_user_has_active_duel_in_chat(chat_id, target_id):
        return False, "📑 Вы уже участвуете в другой дуэли в этом чате."

    if stake_amount > 0 and not _duel_take_materials(int(target_id), int(stake_amount)):
        return False, "📝 У вас недостаточно био-материалов для дуэли со ставкой."

    now = int(now_ts())
    first_turn_id = random.choice([int(challenger_id), int(target_id)])

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")
            c.execute("UPDATE duel_invites SET status='accepted' WHERE invite_id=?", (int(invite_id),))
            c.execute(
                "INSERT INTO duels(invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, current_turn_user_id, turns_done, challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, msg_chat_id, msg_id, ended_at) "
                "VALUES (?,?,?,?,?,?,?,?,0,0,0,'active',0,0,0,0,0)",
                (
                    int(invite_id),
                    int(chat_id),
                    int(challenger_id),
                    int(target_id),
                    int(stake_amount),
                    int(now),
                    int(now + DUEL_TURN_TIMEOUT_SEC),
                    int(first_turn_id),
                )
            )
            duel_id = int(c.lastrowid)
            conn.commit()
        except Exception:
            conn.rollback()
            if stake_amount > 0:
                _duel_refund_materials(int(target_id), int(stake_amount))
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    _duel_cancel_other_invites_for_target(chat_id, target_id, int(invite_id), int(challenger_id))

    db_exec(
        "UPDATE duels SET msg_chat_id=?, msg_id=? WHERE duel_id=?",
        (int(inv["msg_chat_id"] or 0), int(inv["msg_id"] or 0), int(duel_id)),
        commit=True
    )

    fresh_duel = _duel_by_id(int(duel_id))
    txt = _duel_started_text(chat_id, challenger_id, target_id, stake_amount, first_turn_id)
    if edit_invite_message:
        _duel_edit_invite_message(inv, txt, reply_markup=kb_duel_actions(fresh_duel))

    return True, "✅ Дуэль началась."

def _duel_decline_invite(invite_id: int, actor_id: int, *, edit_invite_message: bool = True):
    inv = _duel_invite_by_id(int(invite_id))
    if not inv:
        return False, "📑 Вызов на дуэль не найден."

    if (inv["status"] or "").strip() != "pending":
        return False, "📑 Этот вызов уже неактивен."

    if int(inv["target_id"]) != int(actor_id):
        return False, "📑 Этот вызов адресован не вам."

    db_exec("UPDATE duel_invites SET status='declined' WHERE invite_id=?", (int(invite_id),), commit=True)
    _duel_refund_invite_stake(inv)

    txt = _duel_declined_text(int(inv["chat_id"]), int(inv["challenger_id"]), int(inv["target_id"]))
    if edit_invite_message:
        _duel_edit_invite_message(inv, txt)
    return True, "❎ Вы отказались от дуэли."

def _duel_housekeeping_once(now_value: int):
    now_value = int(now_value)

    pending = db_all(
        "SELECT invite_id, chat_id, challenger_id, target_id, stake_amount, created_at, expires_at, status, msg_chat_id, msg_id "
        "FROM duel_invites "
        "WHERE status='pending' AND expires_at>0 AND expires_at<=? "
        "ORDER BY invite_id ASC",
        (int(now_value),)
    ) or []
    for inv in pending:
        db_exec("UPDATE duel_invites SET status='expired' WHERE invite_id=?", (int(inv["invite_id"]),), commit=True)
        _duel_refund_invite_stake(inv)
        _duel_edit_invite_message(inv, _duel_invite_expired_text())

    active = db_all(
        "SELECT duel_id, invite_id, chat_id, challenger_id, target_id, stake_amount, started_at, next_action_until, current_turn_user_id, turns_done, "
        "challenger_aim_bonus, target_aim_bonus, status, winner_id, loser_id, msg_chat_id, msg_id, ended_at "
        "FROM duels "
        "WHERE status='active' AND next_action_until>0 AND next_action_until<=? "
        "ORDER BY duel_id ASC",
        (int(now_value),)
    ) or []
    for duel in active:
        db_exec(
            "UPDATE duels SET status='cancelled', ended_at=? WHERE duel_id=?",
            (int(now_value), int(duel["duel_id"])),
            commit=True
        )
        _duel_refund_duel_stakes(duel)
        _duel_mark_bets_refunded(int(duel["duel_id"]))
        txt = _duel_inactive_text(int(duel["chat_id"]), int(duel["current_turn_user_id"] or 0))
        _duel_edit_duel_message(duel, txt)

def handle_duel_commands(message, parsed: Parsed):
    if message.chat.type not in ("group", "supergroup"):
        return

    uid = int(message.from_user.id)
    chat_id = int(message.chat.id)

    if parsed.cmd == "duel_stats":
        text = render_duel_stats_text(
            int(chat_id),
            (getattr(message.chat, "title", None) or "").strip()
        )
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd == "duel_bets_list":
        text = render_duel_bets_text(
            int(chat_id),
            int(uid),
            (getattr(message.chat, "title", None) or "").strip()
        )
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd == "duel_bet":
        amount, target_id, target_user_obj, err = _duel_parse_bet_args(message, parsed)
        if target_id is None:
            bot.reply_to(message, err)
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        try:
            ok, msg, duel_row = _duel_place_bet(int(chat_id), int(uid), int(target_id), int(amount))
        except Exception as e:
            send_error_report("duel_bet_place", e)
            bot.reply_to(message, "📑 Не удалось сделать ставку.")
            return

        if not ok:
            if msg == "📝 У вас нет столько био-материалов для ставки.":
                set_balance_chain_state_from_message(
                    message,
                    BALCHAIN_DUEL_BET,
                    "Повторить ставку",
                    {"amount": int(amount), "target_id": int(target_id)}
                )
                bot.reply_to(message, msg, reply_markup=kb_open_balance(int(uid)))
            else:
                bot.reply_to(message, msg)
            return

        with chat_name_context(int(chat_id)):
            target_tag = public_user_tag(int(target_id))

        st = get_balance_chain_state(int(uid))
        if st and str(st.get("chain_kind") or "") == BALCHAIN_DUEL_BET:
            clear_balance_chain_state(int(uid))

        bot.reply_to(
            message,
            f"💰 Вы сделали ставку на дуэлянта <b>{target_tag}</b> в размере 💊 {_duel_stake_text(int(amount))}\n"
            "Дождитесь окончания дуэли. Мы сообщим вам, если ваша ставка сыграет.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd in ("duel_accept", "duel_decline"):
        inv = _duel_latest_pending_invite_for_target(int(chat_id), int(uid))
        if not inv:
            bot.reply_to(message, "📑 В этом чате нет активного вызова на дуэль для вас.")
            return

        try:
            if parsed.cmd == "duel_accept":
                ok, msg = _duel_accept_invite(int(inv["invite_id"]), int(uid), edit_invite_message=False)
                if not ok:
                    if msg == "📝 У вас недостаточно био-материалов для дуэли со ставкой.":
                        bot.reply_to(message, msg, reply_markup=kb_open_balance(int(uid)))
                    else:
                        bot.reply_to(message, msg)
                    return

                duel_row = _duel_active_by_user_in_chat(int(chat_id), int(uid))
                if not duel_row:
                    bot.reply_to(message, "✅ Дуэль началась.")
                    return

                _duel_emit_state(
                    duel_row,
                    _duel_started_text_from_row(duel_row),
                    reply_markup=kb_duel_actions(duel_row),
                    via_message=message,
                    edit_existing=False
                )
                return

            ok, msg = _duel_decline_invite(int(inv["invite_id"]), int(uid), edit_invite_message=False)
            if not ok:
                bot.reply_to(message, msg)
                return

            bot.reply_to(
                message,
                _duel_declined_text(int(inv["chat_id"]), int(inv["challenger_id"]), int(inv["target_id"])),
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return

        except Exception as e:
            send_error_report("duel_accept_decline_text", e)
            bot.reply_to(message, "📑 Не удалось обработать вызов на дуэль.")
            return

    if parsed.cmd == "duel_cancel":
        pending_inv = _duel_latest_outgoing_pending_invite(int(chat_id), int(uid))
        if pending_inv:
            try:
                ok, msg = _duel_cancel_pending_invite(
                    pending_inv,
                    int(uid),
                    via_message=message,
                    edit_existing=False
                )
            except Exception as e:
                send_error_report("duel_cancel_pending_text", e)
                bot.reply_to(message, "📑 Не удалось отменить вызов на дуэль.")
                return
    
            if not ok and msg:
                bot.reply_to(message, msg)
            return
    
        duel_row = _duel_active_by_user_in_chat(int(chat_id), int(uid))
        if not duel_row:
            bot.reply_to(
                message,
                "📑 В этом чате у вас нет активной дуэли.",
                reply_markup=kb_duel_no_active(int(uid))
            )
            return
    
        try:
            ok, msg = _duel_cancel_before_moves(
                duel_row,
                int(uid),
                via_message=message,
                edit_existing=False
            )
        except Exception as e:
            send_error_report("duel_cancel_text", e)
            bot.reply_to(message, "📑 Не удалось отменить дуэль.")
            return
    
        if not ok and msg:
            bot.reply_to(message, msg)
        return
    

    if parsed.cmd in ("duel_fire", "duel_aim", "duel_break_aim", "duel_surrender"):
        duel_row = _duel_active_by_user_in_chat(int(chat_id), int(uid))
        if not duel_row:
            bot.reply_to(
                message,
                "📑 В этом чате у вас нет активной дуэли.",
                reply_markup=kb_duel_no_active(int(uid))
            )
            return

        action_map = {
            "duel_fire": "fire",
            "duel_aim": "aim",
            "duel_break_aim": "break",
            "duel_surrender": "surrender",
        }

        try:
            ok, err = _duel_perform_action(
                duel_row,
                int(uid),
                action_map[parsed.cmd],
                via_message=message,
                edit_existing=False
            )
        except Exception as e:
            send_error_report("duel_action_text", e)
            bot.reply_to(message, "📑 Не удалось выполнить действие дуэли.")
            return

        if not ok and err:
            bot.reply_to(message, err)
        return

    with_stake = (parsed.cmd == "duel_call_stake")
    target_id, target_user_obj, stake_amount, err = _duel_parse_call_args(message, parsed, with_stake=with_stake)
    if target_id is None:
        bot.reply_to(message, err)
        return

    if int(target_id) == int(uid):
        bot.reply_to(message, "📑 Не ищите своёй сменти раньше времени.")
        return

    if target_user_obj is not None and bool(getattr(target_user_obj, "is_bot", False)):
        bot.reply_to(message, "📑 Как бы Вам не хотелось показать своё преимущество перед искуственным соперником, бот не может участвовать в дуэли.")
        return

    my_bot_id = 0
    try:
        me = bot.get_me()
        my_bot_id = int(getattr(me, "id", 0) or 0)
    except Exception:
        my_bot_id = 0
    if my_bot_id and int(target_id) == int(my_bot_id):
        bot.reply_to(message, "📑 Как бы Вам не хотелось показать своё преимущество перед искуственным соперником, бот не может участвовать в дуэли.")
        return

    if _duel_user_has_active_duel_in_chat(int(chat_id), int(uid)) or _duel_user_has_outgoing_pending_invite_in_chat(int(chat_id), int(uid)):
        bot.reply_to(message, "📑 Вы уже участвуете в дуэли или ожидаете ответа на свой вызов в этом чате.")
        return

    if _duel_user_has_active_duel_in_chat(int(chat_id), int(target_id)):
        bot.reply_to(message, "📑 Этот пользователь уже участвует в другой дуэли в этом чате.")
        return

    if stake_amount > 0 and not _duel_take_materials(int(uid), int(stake_amount)):
        set_balance_chain_state_from_message(
            message,
            BALCHAIN_DUEL_STAKE,
            "Повторить вызов",
            {"stake_amount": int(stake_amount), "target_id": int(target_id)}
        )
        bot.reply_to(
            message,
            "📝 У вас недостаточно био-материалов для дуэли со ставкой.",
            reply_markup=kb_open_balance(int(uid))
        )
        return

    st = get_balance_chain_state(int(uid))
    if st and str(st.get("chain_kind") or "") == BALCHAIN_DUEL_STAKE:
        clear_balance_chain_state(int(uid))

    try:
        invite_id = _duel_create_invite(int(chat_id), int(uid), int(target_id), int(stake_amount))
        txt = _duel_invite_text(int(chat_id), int(uid), int(target_id), int(stake_amount))
        sent = bot.reply_to(
            message,
            txt,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_duel_invite(int(invite_id), int(target_id), int(uid))
        )
        _duel_mark_invite_message(int(invite_id), int(sent.chat.id), int(sent.message_id))
    except Exception as e:
        if int(stake_amount or 0) > 0:
            _duel_refund_materials(int(uid), int(stake_amount))
        try:
            db_exec("DELETE FROM duel_invites WHERE invite_id=?", (int(invite_id),), commit=True)
        except Exception:
            pass
        send_error_report("duel_create_invite", e)
        bot.reply_to(message, "📑 Не удалось отправить вызов на дуэль.")
        return

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_RANDOM}:"))
def cb_duel_random(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 2:
            bot.answer_callback_query(cq.id)
            return

        actor_id = int(parts[1] or 0)
        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id)
            return

        if not getattr(cq, "message", None) or not getattr(cq.message, "chat", None):
            bot.answer_callback_query(cq.id)
            return

        chat_id = int(cq.message.chat.id)
        chat_type = (getattr(cq.message.chat, "type", "") or "").lower()
        if chat_type not in ("group", "supergroup"):
            bot.answer_callback_query(cq.id)
            return

        def _edit_current(text: str, rm=None):
            limited_edit_message_text(
                text=text,
                chat_id=int(cq.message.chat.id),
                msg_id=int(cq.message.message_id),
                parse_mode="HTML",
                reply_markup=rm,
                disable_web_page_preview=True
            )

        if _duel_user_has_active_duel_in_chat(int(chat_id), int(actor_id)) or _duel_user_has_any_pending_invite_in_chat(int(chat_id), int(actor_id)):
            _edit_current("📑 Вы уже участвуете в дуэли или ожидаете решения по вызову в этом чате.", rm=None)
            bot.answer_callback_query(cq.id)
            return

        target_id = _duel_pick_random_target(int(chat_id), int(actor_id))
        if target_id <= 0:
            _edit_current(
                "📑 В этом чате не найден подходящий соперник для случайной дуэли.",
                rm=kb_duel_no_active(int(actor_id))
            )
            bot.answer_callback_query(cq.id)
            return

        invite_id = 0
        try:
            invite_id = _duel_create_invite(int(chat_id), int(actor_id), int(target_id), 0)
            txt = _duel_invite_text(int(chat_id), int(actor_id), int(target_id), 0)
            rm = kb_duel_invite(int(invite_id), int(target_id), int(actor_id))

            _edit_current(txt, rm=rm)
            _duel_mark_invite_message(int(invite_id), int(chat_id), int(cq.message.message_id))
        except Exception as e:
            try:
                if int(invite_id or 0) > 0:
                    db_exec("DELETE FROM duel_invites WHERE invite_id=?", (int(invite_id),), commit=True)
            except Exception:
                pass
            send_error_report("cb_duel_random", e)
            _edit_current("📑 Не удалось подобрать достойного соперника для дуэли.", rm=kb_duel_no_active(int(actor_id)))

        bot.answer_callback_query(cq.id)
    except Exception as e:
        send_error_report("cb_duel_random_outer", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_ACCEPT}:"))
def cb_duel_accept(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        invite_id = int(parts[1])
        target_id = int(parts[2])

        if int(cq.from_user.id) != int(target_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        ok, msg = _duel_accept_invite(int(invite_id), int(target_id), edit_invite_message=True)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_accept", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_DECLINE}:"))
def cb_duel_decline(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        invite_id = int(parts[1])
        target_id = int(parts[2])

        if int(cq.from_user.id) != int(target_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        ok, msg = _duel_decline_invite(int(invite_id), int(target_id), edit_invite_message=True)
        bot.answer_callback_query(cq.id, msg, show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_decline", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_FIRE}:"))
def cb_duel_fire(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        duel_row = _duel_by_id(int(duel_id))
        ok, msg = _duel_perform_action(duel_row, int(actor_id), "fire", edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_fire", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_AIM}:"))
def cb_duel_aim(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        duel_row = _duel_by_id(int(duel_id))
        ok, msg = _duel_perform_action(duel_row, int(actor_id), "aim", edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_aim", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_BREAK_AIM}:"))
def cb_duel_break_aim(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        duel_row = _duel_by_id(int(duel_id))
        ok, msg = _duel_perform_action(duel_row, int(actor_id), "break", edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_break_aim", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_SURRENDER}:"))
def cb_duel_surrender(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        duel_row = _duel_by_id(int(duel_id))
        ok, msg = _duel_perform_action(duel_row, int(actor_id), "surrender", edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_surrender", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_INV_CANCEL}:"))
def cb_duel_inv_cancel(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        invite_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        invite_row = _duel_invite_by_id(int(invite_id))
        ok, msg = _duel_cancel_pending_invite(invite_row, int(actor_id), edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "Вызов отменён.", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_inv_cancel", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_CANCEL}:"))
def cb_duel_cancel(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        actor_id = int(parts[2])

        if int(cq.from_user.id) != int(actor_id):
            bot.answer_callback_query(cq.id, "Вы не можете нажимать чужие кнопки!")
            return

        duel_row = _duel_by_id(int(duel_id))
        ok, msg = _duel_cancel_before_moves(duel_row, int(actor_id), edit_existing=True)
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "Дуэль отменена.", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_cancel", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "").startswith(f"{CB_DUEL_REMATCH}:"))
def cb_duel_rematch(cq):
    try:
        parts = (cq.data or "").split(":")
        if len(parts) != 3:
            bot.answer_callback_query(cq.id)
            return

        duel_id = int(parts[1])
        allowed_id = int(parts[2])

        duel_row = _duel_by_id(int(duel_id))
        if not duel_row:
            bot.answer_callback_query(cq.id, "Дуэль не найдена.")
            return

        actor_id = int(cq.from_user.id)

        if int(allowed_id) > 0 and actor_id != int(allowed_id):
            bot.answer_callback_query(cq.id, "Нажать эту кнопку может только проигравший игрок.")
            return

        ok, msg = _duel_start_rematch_from_finished(duel_row, int(actor_id))
        bot.answer_callback_query(cq.id, msg if (not ok and msg) else "Реванш начался.", show_alert=not ok)
    except Exception as e:
        send_error_report("cb_duel_rematch", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

# COMANDS HANDLERS
def handle_owner_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "owner":
        return

    upsert_user(message.from_user)

    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    if not can_manage_owners(uid):
        bot.reply_to(message, "📑 Только создатель бота может назначать агентов.")
        return

    if not parsed.args:
        return

    target_id = resolve_target_id(parsed.args)
    if target_id is None:
        return

    current_creator_id = int(get_current_creator_id())
    if int(target_id) == current_creator_id:
        bot.reply_to(message, "📑 Нельзя назначить текущего создателя старшим агентом через /owner. Используйте /my_owner.")
        return

    if is_owner(int(target_id)):
        bot.reply_to(message, f"📑 Пользователь <code>{int(target_id)}</code> уже является старшим агентом.", parse_mode="HTML")
        return

    add_bot_owner(int(target_id), added_by=uid)
    ensure_lab_exists(int(target_id))

    row = get_user_row(int(target_id))
    disp = display_name(row["first_name"] or "", row["last_name"] or "", row["username"] or "", int(target_id)) if row else str(int(target_id))
    un = (row["username"] or "") if row else ""
    bot.reply_to(
        message,
        f"✅ Пользователь <b>{tg_mention(int(target_id), disp, username=un)}</b> назначен старшим агентом технической поддержки.",
        parse_mode="HTML",
        disable_web_page_preview=True
    )

def handle_infect_command(message, parsed: Parsed, edit_ctx: Optional[dict] = None, actor_user=None):
    if is_channel_sender_message(message):
        return   
    actor = actor_user or message.from_user
    attacker_id = int(actor.id)
    upsert_user(actor)
    _merge_placeholder_to_real_user(actor)
    ensure_lab_exists(attacker_id)
    mark_lab_active(attacker_id)

    def _emit(text: str, reply_markup=None):
        if edit_ctx and isinstance(edit_ctx, dict):
            inline_id = edit_ctx.get("inline_id")
            chat_id = edit_ctx.get("chat_id")
            msg_id = edit_ctx.get("msg_id")
            if inline_id:
                limited_edit_message_text(
                    text=text,
                    inline_id=inline_id,
                    parse_mode="HTML",
                    reply_markup=reply_markup,
                    disable_web_page_preview=True
                )
                return
            if chat_id and msg_id:
                limited_edit_message_text(
                    text=text,
                    chat_id=chat_id,
                    msg_id=msg_id,
                    parse_mode="HTML",
                    reply_markup=reply_markup,
                    disable_web_page_preview=True
                )
                return
        bot.reply_to(message, text, disable_web_page_preview=True, reply_markup=reply_markup)

    if getattr(message, "via_bot", None) is not None:
        return

    req = _parse_infect_request(message, parsed, attacker_id)
    if req.get("kind") == "NONE":
        return   
    now = now_ts()

    def _notify_target(tid: int, text: str):
        tid = int(tid)

        if not is_lab_active(tid):
            return None

        return send_user_notification(tid, text)

    # организатор
    att_un = getattr(actor, "username", "") or ""
    att_fn = getattr(actor, "first_name", "") or ""
    att_ln = getattr(actor, "last_name", "") or ""
    att_disp = display_name(att_fn, att_ln, att_un, attacker_id)
    organizer_tag = tg_mention(attacker_id, att_disp, username=att_un)

    fever_row = db_one(
        "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(fever_pathogen,'') AS fp FROM labs WHERE user_id=?",
        (attacker_id,)
    )
    fever_until = int(fever_row["f"] if fever_row else 0)
    fever_pat = (fever_row["fp"] if fever_row else "") or ""
    if fever_until > now:
        left = fever_until - now
        _f, _fp, vac_cnt = get_fever_and_vaccines(attacker_id)

        if vac_cnt > 0:
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=_cb_use_vaccine(attacker_id), style="primary"))
            _emit(
                f"🌡️ У вас горячка, вызванная {_pat_for_fever(fever_pat)}. Придётся отлежаться, пока она не пройдёт\n"
                f"Время выздоровления {_format_hms(left)}"
                f"\n\n💉 Для быстрого выздоровления используйте вакцину\n"
                f"команда \"<code>Био использовать вакцину</code>\"",
                reply_markup=kb
            )
        else:
            price_txt = _fmt_bio_res(get_vaccine_price(attacker_id))
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=_cb_buy_vaccine(attacker_id), style="primary"))
            _emit(
                f"🌡️ У вас горячка, вызванная {_pat_for_fever(fever_pat)}. Придётся отлежаться, пока она не пройдёт\n"
                f"Время выздоровления {_format_hms(left)}"
                f"\n\n💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: {price_txt}, "
                f"команда \"<code>Био купить вакцину</code>\"",
                reply_markup=kb
            )
        return

    lab_row = db_one(
        "SELECT COALESCE(ready_pathogens,0) AS rp, COALESCE(total_pathogens,1) AS tp, "
        "COALESCE(next_pathogen_in,0) AS npi, COALESCE(qualification,1) AS qual, "
        "COALESCE(pathogen_name,'') AS pn, COALESCE(infectivity,0) AS inf, "
        "COALESCE(lethality,0) AS let, COALESCE(acceleration,0) AS acc, COALESCE(ids,1) AS a_ids "
        "FROM labs WHERE user_id=?",
        (attacker_id,)
    )
    ready = int(lab_row["rp"] if lab_row else 0)
    pathogen_name = (lab_row["pn"] if lab_row else "") or ""
    attacker_inf = int(lab_row["inf"] if lab_row else 0)
    attacker_let = int(lab_row["let"] if lab_row else 0)
    attacker_acc = int(lab_row["acc"] if lab_row else 0)
    inf_days = _calc_inf_days(attacker_let)
    inf_duration_sec = int(inf_days) * 86400
    fever_add = _calc_fever_sec(attacker_let)
    craft_sec, _dup0 = _craft_params(PATHOGEN_CRAFT_SEC, PATHOGEN_MIN_SEC, attacker_acc)
    total_pathogens = int(lab_row["tp"] if lab_row else 1) or 1
    pat_next_price = _level_price(SKILL_N1["PAT"], total_pathogens + 1)
    pat_price_txt = f"🧬 {_ru_dots(pat_next_price)} ({_fmt_k(pat_next_price)})"
    mat_word = _ru_form(int(pat_next_price), "био-материал", "био-материала", "био-материалов")
    pat_price_mat_line = f"{_fmt_k(int(pat_next_price))} {mat_word}"
    attacker_qual = int(lab_row["qual"] if lab_row else 1) or 1
    from_pathogens_summary = bool(edit_ctx.get("pathogens_summary")) if isinstance(edit_ctx, dict) else False

    def _pathogens_extra_line() -> str:
        if not from_pathogens_summary:
            return ""
        rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
        rem = int(rem_row["rp"] if rem_row else 0)
        return f"\n🧪 Осталось патогенов: {rem} из {int(total_pathogens)}"

    def _emit_no_pathogens(inf_ctx: Optional[dict] = None):
        npi = int(_rget(lab_row, "npi", 0) or 0)
        qual = int(_rget(lab_row, "qual", 1) or 1)

        if npi <= 0:
            npi = PATHOGEN_CRAFT_SEC

        eta = time.strftime("%H:%M:%S", time.localtime(now_ts() + max(0, npi)))

        mat_word = _ru_form(pat_next_price, "био-материал", "био-материала", "био-материалов")
        pat_price_line = f"{_fmt_k(pat_next_price)} {mat_word}"

        kb = InlineKeyboardMarkup()

        ctx = inf_ctx or {}
        ctx_kind = str(ctx.get("kind") or "")

        cb_pat_1 = _upg_cb("P", attacker_id, "PAT", 1, "C")
        cb_pat_2 = _upg_cb("P", attacker_id, "PAT", 2, "C")
        cb_pat_5 = _upg_cb("P", attacker_id, "PAT", 5, "C")
        cb_acc_1 = _upg_cb("P", attacker_id, "ACC", 1, "C")
        cb_acc_2 = _upg_cb("P", attacker_id, "ACC", 2, "C")
        cb_acc_5 = _upg_cb("P", attacker_id, "ACC", 5, "C")

        try:
            if ctx_kind == "U":
                t_id = ctx.get("target")
                if t_id is None:
                    tok = str(ctx.get("token") or "").strip()
                    if tok.isdigit():
                        t_id = int(tok)
                if t_id is not None:
                    t_id = int(t_id)
                    cb_pat_1 = _upg_cb_i("P", attacker_id, "PAT", 1, "U", str(t_id))
                    cb_pat_2 = _upg_cb_i("P", attacker_id, "PAT", 2, "U", str(t_id))
                    cb_pat_5 = _upg_cb_i("P", attacker_id, "PAT", 5, "U", str(t_id))
                    cb_acc_1 = _upg_cb_i("P", attacker_id, "ACC", 1, "U", str(t_id))
                    cb_acc_2 = _upg_cb_i("P", attacker_id, "ACC", 2, "U", str(t_id))
                    cb_acc_5 = _upg_cb_i("P", attacker_id, "ACC", 5, "U", str(t_id))
            elif ctx_kind == "M":
                mode = str(ctx.get("mode") or "r")
                flt = str(ctx.get("filter") or "n")
                cb_pat_1 = _upg_cb_i("P", attacker_id, "PAT", 1, "M", mode, flt)
                cb_pat_2 = _upg_cb_i("P", attacker_id, "PAT", 2, "M", mode, flt)
                cb_pat_5 = _upg_cb_i("P", attacker_id, "PAT", 5, "M", mode, flt)
                cb_acc_1 = _upg_cb_i("P", attacker_id, "ACC", 1, "M", mode, flt)
                cb_acc_2 = _upg_cb_i("P", attacker_id, "ACC", 2, "M", mode, flt)
                cb_acc_5 = _upg_cb_i("P", attacker_id, "ACC", 5, "M", mode, flt)
        except Exception:
            pass

        
        kb.row(
            _ikb_premium_counter("🧪", "× 1", callback_data=cb_pat_1),
            _ikb_premium_counter("🧪", "× 2", callback_data=cb_pat_2),
            _ikb_premium_counter("🧪", "× 5", callback_data=cb_pat_5),
        )
        kb.row(
            _ikb_premium_counter("🧫", "× 1", callback_data=cb_acc_1),
            _ikb_premium_counter("🧫", "× 2", callback_data=cb_acc_2),
            _ikb_premium_counter("🧫", "× 5", callback_data=cb_acc_5),
        )

        _emit(
            "📝 Закончились все патогены\n"
            f"⏱️ Новый через {_format_hms(npi)} ({eta})\n"
            f"🧪 Ячеек для патогенов: {total_pathogens} | +1 = {pat_price_line}\n"
            f"👨‍🔬 Квалификация учёных: {qual} ур ({_format_hm_from_seconds(craft_sec)})\n"
            "💬 Вы также можете заказать дополнительные ячейки с патогенами в лабораторию командой "
            "\"<code>Био +патоген</code>\" + количество необходимых ячеек",
            reply_markup=kb
        )

    if ready <= 0:
        _emit_no_pathogens(req)
        return
    
    def _apply_limit(cnt: int) -> int:
        cnt = int(cnt) if cnt else 1
        if cnt < 1:
            cnt = 1
        if cnt > 10:
            cnt = 10
        if cnt > ready:
            cnt = ready
        return cnt

    # ФИКС ЦЕЛЬ (reply/@/id): серия попыток по 1 объекту
    if req["kind"] == "U":
        target_user_obj = None
        token = req.get("token", "")
        target_id: Optional[int] = req.get("target")

        if target_id is None and token:
            target_id = _resolve_or_create_infect_target(token)

        if target_id is None:
            _emit("📑 Цель для заражения не найдена.")
            return

        if is_bot_target(target_id, target_user_obj, token):
            _emit("📑 Объект заражения не подвержен заражению. Вы не можете заразить бота.")
            return
        if int(target_id) == int(attacker_id):
            _emit("🧪 Вы не можете заразить самого себя.")
            return
        if same_corp(int(attacker_id), int(target_id)):
            _emit("📑 Участники одной Корпорации не могут заражать друг друга.")
            return

        if message.chat.type == "private" and not is_lab_active(int(target_id)):
            _emit(
                "📝 Объект ещё не создал свою лабораторию.\n\n"
                "💬 Вы можете первый раз заразить его только в общей с вами беседе.\n"
                "Либо пригласите его присоединиться к мини-игре «Био-атака», попросив его ввести команду \"<code>Био лаб</code>\""
            )
            return

        ensure_lab_exists(int(target_id))

        cnt = _apply_limit(req.get("count", 1))
        if cnt <= 0:
            _emit_no_pathogens({"kind": "U", "target": int(target_id)})
            return

        cd_row = db_one(
            "SELECT COALESCE(until_ts,0) AS u FROM infection_cooldowns WHERE attacker_id=? AND target_id=?",
            (attacker_id, int(target_id))
        )
        cd_until = int(cd_row["u"] if cd_row else 0)
        if cd_until > now:
            left = cd_until - now
            _emit(
                "🩻 Недавно Вы уже подвергали заражению выбранный объект.\n"
                f"⏱️ Следующая возможность появится через {_format_hms(left)} ({_fmt_clock_hms(cd_until)})"
            )
            return

        used = 0
        success = False
        gained = 0

        trow = db_one(
            "SELECT COALESCE(immunity,0) AS imm, COALESCE(bio_exp,0) AS be, COALESCE(ids,1) AS t_ids FROM labs WHERE user_id=?",
            (int(target_id),)
        )
        tgt_imm = int(trow["imm"] if trow else 0)
        p_success = infect_success_chance(attacker_inf, tgt_imm)
        rand_evt = False
        rand_evt_text = ""
        rand_evt_pct = random_event_pct(attacker_qual)
        immune_fail = 0
        fail_stack = _get_infection_fail_stack(attacker_id, int(target_id), now)

        for i in range(1, cnt + 1):
            used = i
            if random.random() * 100.0 < rand_evt_pct:
                rand_evt = True
                rand_evt_text = pick_random_event_text()
                break

            roll = random.random() * 100.0
            if roll >= p_success:
                immune_fail += 1
                fail_stack = _add_infection_fail_stack(attacker_id, int(target_id), now)
                continue
            if roll <= p_success:
                success = True
                texp = int(trow["be"] if trow else 0)
                gained = _calc_infection_gain_with_fail_stack(texp, fail_stack)

                seen = db_one(
                    "SELECT 1 FROM infection_seen WHERE attacker_id=? AND target_id=? LIMIT 1",
                    (attacker_id, int(target_id))
                )
                first_time = (seen is None)

                active = db_one(
                    "SELECT end_ts, counted FROM infections WHERE attacker_id=? AND target_id=?",
                    (attacker_id, int(target_id))
                )
                already_active = False
                if active:
                    end_ts0 = int(active["end_ts"] or 0)
                    counted0 = int(active["counted"] or 0)
                    if counted0 == 1 and end_ts0 > now:
                        already_active = True

                end_ts = now + inf_duration_sec
                next_payout = now + 86400
                if next_payout >= end_ts:
                    next_payout = 0

                with DB_LOCK:
                    c = conn.cursor()
                    try:
                        c.execute("BEGIN")

                        c.execute(
                            "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0) >= ? "
                            "THEN ready_pathogens-? ELSE 0 END "
                            "WHERE user_id=?",
                            (used, used, attacker_id)
                        )

                        c.execute(
                            "UPDATE labs SET "
                            "bio_exp=COALESCE(bio_exp,0)+?, "
                            "all_bio_res=COALESCE(all_bio_res,0)+?, "
                            "successful_ops=COALESCE(successful_ops,0)+1, "
                            "ops_total=COALESCE(ops_total,0)+? "
                            "WHERE user_id=?",
                            (gained, gained, used, attacker_id)
                        )

                        c.execute(
                            "UPDATE labs SET bio_exp=CASE "
                            "WHEN COALESCE(bio_exp,0) <= 1 THEN COALESCE(bio_exp,0) "
                            "WHEN (COALESCE(bio_exp,0) - ?) < 1 THEN 1 "
                            "ELSE (COALESCE(bio_exp,0) - ?) END "
                            "WHERE user_id=?",
                            (gained, gained, int(target_id))
                        )

                        c.execute(
                            "UPDATE labs SET defended_total=COALESCE(defended_total,0)+?, prevented_ops=COALESCE(prevented_ops,0)+? "
                            "WHERE user_id=?",
                            (used, immune_fail, int(target_id))
                        )

                        c.execute(
                            "UPDATE labs SET "
                            "fever_until_ts = CASE WHEN COALESCE(fever_until_ts,0) > ? THEN fever_until_ts + ? ELSE ? END, "
                            "fever_pathogen = ? "
                            "WHERE user_id=?",
                            (now, fever_add, now + fever_add, (pathogen_name or "").strip(), int(target_id))
                        )

                        if not already_active:
                            c.execute("UPDATE labs SET infected_total=COALESCE(infected_total,0)+1 WHERE user_id=?", (attacker_id,))
                            c.execute("UPDATE labs SET diseases_total=COALESCE(diseases_total,0)+1 WHERE user_id=?", (int(target_id),))

                        c.execute(
                            "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name,known_to_target) "
                            "VALUES (?,?,?,?,?,?,1,?,0) "
                            "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                            "start_ts=excluded.start_ts, end_ts=excluded.end_ts, "
                            "add_bio_res=excluded.add_bio_res, "
                            "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name",
                            (attacker_id, int(target_id), now, end_ts, gained, next_payout, (pathogen_name or "").strip())
                        )

                        c.execute(
                            "INSERT INTO infection_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
                            "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
                            (attacker_id, int(target_id), now + REINFECT_CD_SEC)
                        )

                        c.execute(
                            "DELETE FROM infection_fail_stacks WHERE attacker_id=? AND target_id=?",
                            (attacker_id, int(target_id))
                        )

                        if first_time:
                            c.execute(
                                "INSERT OR IGNORE INTO infection_seen(attacker_id,target_id,first_ts) VALUES (?,?,?)",
                                (attacker_id, int(target_id), now)
                            )

                        conn.commit()
                    except Exception:
                        conn.rollback()
                        raise
                    finally:
                        try:
                            c.close()
                        except Exception:
                            pass

                try:
                    ur_t = get_user_row(int(target_id))
                    tgt_un = (ur_t["username"] or "") if ur_t else ""
                    tgt_fn = (ur_t["first_name"] or "") if ur_t else ""
                    tgt_ln = (ur_t["last_name"] or "") if ur_t else ""
                    tgt_disp = display_name(tgt_fn, tgt_ln, tgt_un, int(target_id))
                    target_tag = tg_mention(int(target_id), tgt_disp, username=tgt_un)
                    notify_chat_id, notify_off = get_notify_prefs(int(target_id))
                    if not (int(notify_off) == 1 and int(notify_chat_id) == 0):
                        target_notice = (
                            f"🦠 Кто-то подверг заражению {_pat_for_text((pathogen_name or '').strip())} {target_tag}\n"
                            f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                            f"🤒 Заражение на {_format_days(inf_days)}"
                        )
                        if first_time:
                            target_notice += (
                                "\n\n👨‍🔬 "
                                + _gender_pick(
                                    int(target_id),
                                    "infect_first_time_target",
                                    amount=_fmt_bio_res_after_po(int(gained))
                                )
                            )
                        
                        att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
                        tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
                        
                        if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                            exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
                            result_text = (
                                f"🦠 {organizer_tag} {_gender_pick(int(attacker_id), 'infect_exposed')} {_pat_for_text((pathogen_name or '').strip())} {target_tag}\n"
                                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                                f"🤒 Заражение на {_format_days(inf_days)}\n"
                                f"☣️ +{_fmt_k(int(gained))} {exp_word}"
                            )
                            if first_time:
                                result_text += (
                                    "\n\n👨‍🔬 "
                                    + _gender_pick(
                                        int(target_id),
                                        "infect_first_time_target",
                                        amount=_fmt_bio_res_after_po(int(gained))
                                    )
                                )
                        
                            ids_text = render_ids_report(
                                target_id=int(target_id),
                                attempts=int(used),
                                kind="infect",
                                organizer_tag=organizer_tag,
                                result_text=result_text
                            )
                            ids_msg = _notify_target(int(target_id), ids_text)
                            if ids_msg:
                                db_exec(
                                    "UPDATE infections SET known_to_target=1 WHERE attacker_id=? AND target_id=?",
                                    (int(attacker_id), int(target_id)),
                                    commit=True
                                )
                                autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
                        else:
                            _notify_target(int(target_id), target_notice)
                except Exception:
                    pass

                break

        if not success:
            used = cnt
            with DB_LOCK:
                c = conn.cursor()
                try:
                    c.execute("BEGIN")
                    c.execute(
                        "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0) >= ? "
                        "THEN ready_pathogens-? ELSE 0 END, "
                        "ops_total=COALESCE(ops_total,0)+? "
                        "WHERE user_id=?",
                        (used, used, used, attacker_id)
                    )
                    c.execute(
                        "UPDATE labs SET defended_total=COALESCE(defended_total,0)+?, prevented_ops=COALESCE(prevented_ops,0)+? "
                        "WHERE user_id=?",
                        (used, immune_fail, int(target_id))
                    )
                    conn.commit()
                except Exception:
                    conn.rollback()
                    raise
                finally:
                    try:
                        c.close()
                    except Exception:
                        pass

        att_disp = user_full_name(actor)
        att_un = getattr(actor, "username", "") or ""
        attacker_tag = tg_mention(attacker_id, att_disp, username=att_un)

        target_tag = public_user_tag(int(target_id))

        pat_txt = f"«{h(pathogen_name.strip())}»" if (pathogen_name or "").strip() else "неизвестным патогеном"

        header = ""
        if cnt > 1:
            header = (
                "📋 Отчёт об операции заражения объекта:\n"
                f"Использовано патогенов: {used}\n\n"
            )
        
        if rand_evt:
            rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
            rem = int(rem_row["rp"] if rem_row else 0)
            att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
            tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
            ids_sent = False
            if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                result_text = (
                    f"💢 Попытка заразить «{target_tag}» провалилась...\n"
                    f"{h(rand_evt_text)}"
                )
                ids_text = render_ids_report(
                    target_id=int(target_id),
                    attempts=int(used),
                    kind="infect",
                    organizer_tag=organizer_tag,
                    result_text=result_text
                )
                ids_msg = _notify_target(int(target_id), ids_text)
                if ids_msg:
                    ids_sent = True
                    autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
            _emit(
                header +
                f"💢 Попытка заразить «{target_tag}» провалилась...\n"
                f"{h(rand_evt_text)}\n"
                f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_mat_line}",
                reply_markup=kb_infect_retry_user(attacker_id, int(target_id))
            )
            if (not ids_sent) and message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
                reply_mid = 0
                if edit_ctx and isinstance(edit_ctx, dict):
                    reply_mid = int(edit_ctx.get("msg_id") or 0)
                if reply_mid <= 0:
                    reply_mid = int(getattr(message, "message_id", 0) or 0)
                autoanswer_trigger(int(target_id), attacker_id, int(message.chat.id), reply_mid, "CHAT")
            return

        if success:
            exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
            txt = (
                header +
                f"🦠 {attacker_tag} {_gender_pick(int(attacker_id), 'infect_exposed')} {_pat_for_text((pathogen_name or '').strip())} {target_tag}\n"
                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                f"🤒 Заражение на {_format_days(inf_days)}\n"
                f"☣️ +{_fmt_k(int(gained))} {exp_word}"
            )
            txt += _pathogens_extra_line()
            if first_time:
                txt += (
                    "\n\n👨‍🔬 "
                    + _gender_pick(
                        int(attacker_id),
                        "infect_first_time_actor",
                        amount=_fmt_bio_res_after_po(int(gained))
                    )
                )
            _emit(txt)
            att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
            tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
            ids_possible = ids_should_fire(att_ids_lvl, tgt_ids_lvl)

            if (not ids_possible) and message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
                reply_mid = 0
                if edit_ctx and isinstance(edit_ctx, dict):
                    reply_mid = int(edit_ctx.get("msg_id") or 0)
                if reply_mid <= 0:
                    reply_mid = int(getattr(message, "message_id", 0) or 0)
                autoanswer_trigger(int(target_id), attacker_id, int(message.chat.id), reply_mid, "CHAT")
            return
        att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
        tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
        ids_sent = False
        if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
            result_text = (
                f"🥽 Иммунитет объекта «{target_tag}» оказался стойким к вашему патогену.\n"
                "Антитела смогли справиться с заражением."
            )
            ids_text = render_ids_report(
                target_id=int(target_id),
                attempts=int(used),
                kind="infect",
                organizer_tag=organizer_tag,
                result_text=result_text
            )
            ids_msg = _notify_target(int(target_id), ids_text)
            if ids_msg:
                ids_sent = True
                autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
        rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
        rem = int(rem_row["rp"] if rem_row else 0)
        _emit(
            header +
            f"🥽 Иммунитет объекта «{target_tag}» оказался стойким к вашему патогену.\n"
            "Антитела смогли справиться с заражением.\n"
            f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_txt}",
            reply_markup=kb_infect_retry_user_upg(attacker_id, int(target_id))
        )
        if (not ids_sent) and message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
            reply_mid = 0
            if edit_ctx and isinstance(edit_ctx, dict):
                reply_mid = int(edit_ctx.get("msg_id") or 0)
            if reply_mid <= 0:
                reply_mid = int(getattr(message, "message_id", 0) or 0)
            autoanswer_trigger(int(target_id), attacker_id, int(message.chat.id), reply_mid, "CHAT")
        return

    # МАССОВОЕ ПО ПЕРЕМЕННОЙ (р/+/-/чат)
    mode = req.get("mode", "r")
    chat_filter = req.get("filter", "n")

    chat_id = int(message.chat.id) if message.chat.type in ("group", "supergroup") else 0
    if mode == "c" and chat_id == 0:
        return

    def _single_random_retry_kb():
        if mode in ("r", "p", "m", "e"):
            return kb_infect_retry_mass(attacker_id, mode, chat_filter)
        return None

    cnt = _apply_limit(req.get("count", 1))
    if cnt <= 0:
        _emit_no_pathogens({"kind": "M", "mode": mode, "filter": chat_filter})
        return

    used = 0
    att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
    succ = 0
    fail = 0
    first_cnt = 0
    total_gained = 0
    exclude: set[int] = set()
    last_tid: Optional[int] = None
    last_success: bool = False
    last_dummy: bool = False
    last_gained: int = 0
    last_first_time: bool = False

    succ_tags: list[str] = []
    first_tags: list[str] = []
    fail_tags: list[str] = []

    def _mass_target_tag(tid: Optional[int], dummy: bool = False) -> str:
        if dummy or tid is None:
            return "неизвестный пользователь"
        return public_user_tag(int(tid))

    evt_fail: int = 0
    rand_evt_pct = random_event_pct(attacker_qual)
    last_evt: bool = False
    last_evt_text: str = ""

    for _i in range(cnt):
        tid = _pick_target_from_db(attacker_id, mode, chat_id, chat_filter, exclude)
        if tid is None:
            if mode == "r":
                used += 1
                succ += 1
                total_gained += 1
                last_tid = None
                last_success = True
                last_dummy = True
                last_gained = 1
                last_first_time = True

                dummy_tag = _mass_target_tag(None, True)
                succ_tags.append(dummy_tag)
                first_tags.append(dummy_tag)

                with DB_LOCK:
                    c = conn.cursor()
                    try:
                        c.execute("BEGIN")
                        c.execute(
                            "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0)>0 THEN ready_pathogens-1 ELSE 0 END, "
                            "bio_exp=COALESCE(bio_exp,0)+1, all_bio_res=COALESCE(all_bio_res,0)+1, "
                            "successful_ops=COALESCE(successful_ops,0)+1, ops_total=COALESCE(ops_total,0)+1 "
                            "WHERE user_id=?",
                            (attacker_id,)
                        )
                        dummy_tid = -int(now_ts()) - used
                        end_ts = now + inf_duration_sec
                        c.execute(
                            "INSERT OR REPLACE INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name) "
                            "VALUES (?,?,?,?,?,?,0,?)",
                            (attacker_id, dummy_tid, now, end_ts, 0, 0, (pathogen_name or "").strip())
                        )
                        conn.commit()
                    except Exception:
                        conn.rollback()
                        raise
                    finally:
                        try:
                            c.close()
                        except Exception:
                            pass
                continue
            break

        exclude.add(int(tid))

        if is_bot_target(tid, None, "") or int(tid) == int(attacker_id):
            continue

        used += 1

        ensure_lab_exists(int(tid))
        chosen_tag = _mass_target_tag(int(tid))

        trow = db_one(
            "SELECT COALESCE(immunity,0) AS imm, COALESCE(bio_exp,0) AS be, COALESCE(ids,1) AS t_ids FROM labs WHERE user_id=?",
            (int(tid),)
        )
        tgt_imm = int(trow["imm"] if trow else 0)
        p_success = infect_success_chance(attacker_inf, tgt_imm)
        fail_stack = _get_infection_fail_stack(attacker_id, int(tid), now)
        
        if random.random() * 100.0 < rand_evt_pct:
            evt_fail += 1
            fail += 1
            last_tid = int(tid)
            last_success = False
            last_dummy = False
            last_gained = 0
            last_first_time = False
            last_evt = True
            last_evt_text = pick_random_event_text()
            fail_tags.append(chosen_tag)
        
            db_exec(
                "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0)>0 THEN ready_pathogens-1 ELSE 0 END, "
                "ops_total=COALESCE(ops_total,0)+1 WHERE user_id=?",
                (attacker_id,),
                commit=True
            )
            db_exec(
                "UPDATE labs SET defended_total=COALESCE(defended_total,0)+1 WHERE user_id=?",
                (int(tid),),
                commit=True
            )
            tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
            if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                urx = get_user_row(int(tid))
                t_un = (urx["username"] or "") if urx else ""
                t_disp = display_name(
                    (urx["first_name"] or "") if urx else "",
                    (urx["last_name"] or "") if urx else "",
                    t_un,
                    int(tid)
                )
                t_tag = tg_mention(int(tid), t_disp, username=t_un)
                
                result_text = (
                    f"💢 Попытка заразить «{t_tag}» провалилась...\n"
                    f"{h(last_evt_text)}"
                )
                ids_text = render_ids_report(
                    target_id=int(tid),
                    attempts=1,
                    kind="infect",
                    organizer_tag=organizer_tag,
                    result_text=result_text
                )
                ids_msg = _notify_target(int(tid), ids_text)
                if ids_msg:
                    autoanswer_trigger(int(tid), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
            continue
        
        last_evt = False
        roll = random.random() * 100.0

        if roll >= p_success:
            fail += 1
            last_tid = int(tid)
            last_success = False
            last_dummy = False
            last_gained = 0
            last_first_time = False
            fail_tags.append(chosen_tag)
            _add_infection_fail_stack(attacker_id, int(tid), now)           
            db_exec(
                "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0)>0 THEN ready_pathogens-1 ELSE 0 END, "
                "ops_total=COALESCE(ops_total,0)+1 WHERE user_id=?",
                (attacker_id,),
                commit=True
            )
            db_exec(
                "UPDATE labs SET defended_total=COALESCE(defended_total,0)+1, prevented_ops=COALESCE(prevented_ops,0)+1 WHERE user_id=?",
                (int(tid),),
                commit=True
            )
            tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
            if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                result_text = (
                    f"🥽 Иммунитет объекта «{chosen_tag}» оказался стойким к вашему патогену.\n"
                    "Антитела смогли справиться с заражением."
                )
                ids_text = render_ids_report(
                    target_id=int(tid),
                    attempts=1,
                    kind="infect",
                    organizer_tag=organizer_tag,
                    result_text=result_text
                )
                ids_msg = _notify_target(int(tid), ids_text)
                if ids_msg:
                    autoanswer_trigger(int(tid), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
            continue

        succ += 1
        succ_tags.append(chosen_tag)

        texp = int(trow["be"] if trow else 0)
        gained = _calc_infection_gain_with_fail_stack(texp, fail_stack)
        total_gained += gained
        last_tid = int(tid)
        last_success = True
        last_dummy = False
        last_gained = int(gained)

        seen = db_one(
            "SELECT 1 FROM infection_seen WHERE attacker_id=? AND target_id=? LIMIT 1",
            (attacker_id, int(tid))
        )
        ft = (seen is None)
        last_first_time = bool(ft)
        if ft:
            first_cnt += 1
            first_tags.append(chosen_tag)

        active = db_one(
            "SELECT end_ts, counted FROM infections WHERE attacker_id=? AND target_id=?",
            (attacker_id, int(tid))
        )
        already_active = False
        if active:
            end_ts0 = int(active["end_ts"] or 0)
            counted0 = int(active["counted"] or 0)
            if counted0 == 1 and end_ts0 > now:
                already_active = True

        end_ts = now + inf_duration_sec
        next_payout = now + 86400
        if next_payout >= end_ts:
            next_payout = 0

        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")
                c.execute(
                    "UPDATE labs SET ready_pathogens=CASE WHEN COALESCE(ready_pathogens,0)>0 THEN ready_pathogens-1 ELSE 0 END, "
                    "bio_exp=COALESCE(bio_exp,0)+?, all_bio_res=COALESCE(all_bio_res,0)+?, "
                    "successful_ops=COALESCE(successful_ops,0)+1, ops_total=COALESCE(ops_total,0)+1 "
                    "WHERE user_id=?",
                    (gained, gained, attacker_id)
                )
                c.execute(
                    "UPDATE labs SET bio_exp=CASE WHEN COALESCE(bio_exp,0) >= ? THEN bio_exp-? ELSE 0 END WHERE user_id=?",
                    (gained, gained, int(tid))
                )
                c.execute(
                    "UPDATE labs SET fever_until_ts = CASE WHEN COALESCE(fever_until_ts,0) > ? THEN fever_until_ts + ? ELSE ? END, "
                    "fever_pathogen = ? WHERE user_id=?",
                    (now, fever_add, now + fever_add, (pathogen_name or "").strip(), int(tid))
                )
                if not already_active:
                    c.execute("UPDATE labs SET infected_total=COALESCE(infected_total,0)+1 WHERE user_id=?", (attacker_id,))
                    c.execute("UPDATE labs SET diseases_total=COALESCE(diseases_total,0)+1 WHERE user_id=?", (int(tid),))

                c.execute(
                    "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name,known_to_target) "
                    "VALUES (?,?,?,?,?,?,1,?,0) "
                    "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                    "start_ts=excluded.start_ts, end_ts=excluded.end_ts, "
                    "add_bio_res=excluded.add_bio_res, "
                    "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name",
                    (attacker_id, int(tid), now, end_ts, gained, next_payout, (pathogen_name or "").strip())
                )

                c.execute(
                    "INSERT INTO infection_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
                    "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
                    (attacker_id, int(tid), now + REINFECT_CD_SEC)
                )
                c.execute(
                    "DELETE FROM infection_fail_stacks WHERE attacker_id=? AND target_id=?",
                    (attacker_id, int(tid))
                )
                if ft:
                    c.execute(
                        "INSERT OR IGNORE INTO infection_seen(attacker_id,target_id,first_ts) VALUES (?,?,?)",
                        (attacker_id, int(tid), now)
                    )
                c.execute(
                    "UPDATE labs SET defended_total=COALESCE(defended_total,0)+1 WHERE user_id=?",
                    (int(tid),)
                )
                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass
        try:
            tgt_tag = public_user_tag(int(tid))

            notify_chat_id, notify_off = get_notify_prefs(int(tid))
            if not (int(notify_off) == 1 and int(notify_chat_id) == 0):
                notice = (
                    f"🦠 Кто-то подверг заражению {_pat_for_text((pathogen_name or '').strip())} {tgt_tag}\n"
                    f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                    f"🤒 Заражение на {_format_days(inf_days)}"
                )
                if ft:
                    notice += (
                        "\n\n👨‍🔬 "
                        + _gender_pick(
                            int(tid),
                            "infect_first_time_target",
                            amount=_fmt_bio_res_after_po(int(gained))
                        )
                    )
                tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
                if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                    exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
                    result_text = (
                        f"🦠 {organizer_tag} {_gender_pick(int(attacker_id), 'infect_exposed')} {_pat_for_text((pathogen_name or '').strip())} {tgt_tag}\n"
                        f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                        f"🤒 Заражение на {_format_days(inf_days)}\n"
                        f"☣️ +{_fmt_k(int(gained))} {exp_word}"
                    )
                    if ft:
                        result_text += (
                            "\n\n👨‍🔬 "
                            + _gender_pick(
                                int(attacker_id),
                                "infect_first_time_actor",
                                amount=_fmt_bio_res_after_po(int(gained))
                            )
                        )
                    ids_text = render_ids_report(
                        target_id=int(tid),
                        attempts=1,
                        kind="infect",
                        organizer_tag=organizer_tag,
                        result_text=result_text
                    )
                    ids_msg = _notify_target(int(tid), ids_text)
                    if ids_msg:
                        db_exec(
                            "UPDATE infections SET known_to_target=1 WHERE attacker_id=? AND target_id=?",
                            (int(attacker_id), int(tid)),
                            commit=True
                        )
                        autoanswer_trigger(int(tid), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
                else:
                    _notify_target(int(tid), notice)
        except Exception:
            pass

    if used <= 0:
        if mode == "c":
            known_cnt = _known_chat_member_count(int(chat_id), int(attacker_id))
            if known_cnt <= 0:
                _emit(
                    "📑 Бот пока не знает участников этого чата для команды \"<code>заразить чат</code>.\"\n\n"
                    "В связи с ограничениями Telegram Bot API.\n"
                    "💬 Для большей эффективности в запоминании новых пользователей, рекомаендую использовать команду \"<code>заразить</code>\" в ответ на сообщение другого игрока."
                )
            else:
                _emit("📑 Подходящая цель в этом чате не найдена.")
        else:
            _emit("📑 Цель для заражения не найдена.")
        return
    
    if cnt == 1 and used == 1:
        att_disp = user_full_name(actor)
        att_un = getattr(actor, "username", "") or ""
        attacker_tag = tg_mention(attacker_id, att_disp, username=att_un)
    
        if last_dummy or (last_tid is None):
            single_target_tag = "неизвестный пользователь"
        else:
            single_target_tag = public_user_tag(int(last_tid))

        if last_evt:
            rem_row = db_one(
                "SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?",
                (attacker_id,)
            )
            rem = int(rem_row["rp"] if rem_row else 0)

            _emit(
                f"💢 Попытка заразить «{single_target_tag}» провалилась...\n"
                f"{h(last_evt_text)}\n"
                f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_mat_line}",
                reply_markup=_single_random_retry_kb()
            )
            return

        if last_success:
            exp_word = _ru_form(int(last_gained), "био-опыт", "био-опыта", "био-опыта")
            txt = (
                f"🦠 {attacker_tag} {_gender_pick(int(attacker_id), 'infect_exposed')} {_pat_for_text((pathogen_name or '').strip())} {single_target_tag}\n"
                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                f"🤒 Заражение на {_format_days(inf_days)}\n"
                f"☣️ +{_fmt_k(int(last_gained))} {exp_word}"
            )
            if last_first_time or last_dummy:
                txt += (
                    "\n\n👨‍🔬 "
                    + _gender_pick(
                        int(attacker_id),
                        "infect_first_time_actor",
                        amount=_fmt_bio_res_after_po(int(last_gained))
                    )
                )
            _emit(txt, reply_markup=_single_random_retry_kb())
            return

        rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
        rem = int(rem_row["rp"] if rem_row else 0)
        _emit(
            f"🥽 Иммунитет объекта «{single_target_tag}» оказался стойким к вашему патогену.\n"
            "Антитела смогли справиться с заражением.\n"
            f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_txt}",
            reply_markup=_single_random_retry_kb()
        )
        
        if message.chat.type in ("group", "supergroup") and last_tid and last_tid > 0 and _chat_has_user(message.chat.id, int(last_tid)):
            reply_mid = 0
            if edit_ctx and isinstance(edit_ctx, dict):
                reply_mid = int(edit_ctx.get("msg_id") or 0)
            if reply_mid <= 0:
                reply_mid = int(getattr(message, "message_id", 0) or 0)
            autoanswer_trigger(int(last_tid), attacker_id, int(message.chat.id), reply_mid, "CHAT")
        return

    def _list_block(tags: list[str]) -> str:
        if not tags:
            return ""
        return "<blockquote>" + "\n".join(tags) + "</blockquote>\n"

    txt = (
        "📋 Отчёт об операции массового заражения объектов:\n"
        f"Использовано патогенов: {used}\n\n"
        f"🦠 Успешно заражено: {succ}\n"
    )
    if succ_tags:
        txt += _list_block(succ_tags)

    if first_cnt > 0:
        txt += f"🩻 Заражено впервые: {first_cnt}\n"
        if first_tags:
            txt += _list_block(first_tags)

    txt += f"❌ Неудачные заражения: {fail}\n"
    if fail_tags:
        txt += _list_block(fail_tags)

    if succ > 0:
        bio_word = _ru_form(total_gained, "био-опыт", "био-опыта", "био-опыта")
        txt += f"\n☣️‍ +{_fmt_k(total_gained)} {bio_word}"

    txt += _pathogens_extra_line()

    _emit(txt, reply_markup=kb_infect_retry_mass(attacker_id, mode, chat_filter))

def handle_sabotage_command(message, parsed: Parsed, edit_ctx: Optional[dict] = None, actor_user=None):
    actor = actor_user or message.from_user
    attacker_id = int(actor.id)
    upsert_user(actor)
    _merge_placeholder_to_real_user(actor)
    ensure_lab_exists(attacker_id)
    mark_lab_active(attacker_id)

    def _emit(text: str, reply_markup=None):
        if edit_ctx and isinstance(edit_ctx, dict):
            inline_id = edit_ctx.get("inline_id")
            chat_id = edit_ctx.get("chat_id")
            msg_id = edit_ctx.get("msg_id")
            if inline_id:
                limited_edit_message_text(text=text, inline_id=inline_id, parse_mode="HTML",
                                          reply_markup=reply_markup, disable_web_page_preview=True)
                return
            if chat_id and msg_id:
                limited_edit_message_text(text=text, chat_id=chat_id, msg_id=msg_id, parse_mode="HTML",
                                          reply_markup=reply_markup, disable_web_page_preview=True)
                return
        bot.reply_to(message, text, disable_web_page_preview=True, reply_markup=reply_markup)

    target_id, target_user = resolve_target_from_reply_or_args(message, parsed)
    if not target_id:
        return

    if (target_user and getattr(target_user, "is_bot", False)) or (int(target_id) == int(bot.get_me().id)):
        _emit("📑 Как бы не сильна ваша вражда к ботам, вы не сможете навредить боту.")
        return

    if int(target_id) == int(attacker_id):
        _emit("📑 Ты не туда воюешь.")
        return

    ensure_lab_exists(int(target_id))
    if not is_lab_active(int(target_id)):
        _emit("📑 Этот пользователь ещё не создал свою лабораторию.")
        return

    now = now_ts()

    cd = db_one(
        "SELECT until_ts FROM sabotage_cooldowns WHERE attacker_id=? AND target_id=?",
        (attacker_id, int(target_id))
    )
    until_ts = int(cd["until_ts"] if cd else 0)
    if until_ts > now:
        left = until_ts - now
        eta = time.strftime("%H:%M:%S", time.localtime(until_ts))
        _emit(
            "🥷 Недавно Вы уже проводили диверсию против выбранного объекта.\n"
            f"⏱️ Следующая возможность появится через {_format_hms(left)} ({eta})"
        )
        return

    a = db_one(
        "SELECT COALESCE(reaction,1) AS rea, COALESCE(ids,1) AS a_ids "
        "FROM labs WHERE user_id=?",
        (attacker_id,)
    )
    t = db_one(
        "SELECT COALESCE(ips,1) AS ips, COALESCE(ids,1) AS t_ids, "
        "COALESCE(ready_pathogens,0) AS rp, COALESCE(total_pathogens,1) AS tp, COALESCE(next_pathogen_in,0) AS npi, "
        "COALESCE(ready_vaccines,0) AS rv, COALESCE(total_vaccines,1) AS tv, COALESCE(next_vaccine_in,0) AS nvi, "
        "COALESCE(all_bio_res,0) AS ar, COALESCE(all_bio_mater,0) AS am, COALESCE(bio_res,0) AS br "
        "FROM labs WHERE user_id=?",
        (int(target_id),)
    )
    if not a or not t:
        return

    a_rea = int(a["rea"] or 1)
    a_ids = int(a["a_ids"] or 1)

    t_ips = int(t["ips"] or 1)
    t_ids = int(t["t_ids"] or 1)

    p = _calc_sabotage_success_pct(a_rea, t_ips)
    fail_p = 100.0 - float(p)

    ur_t = get_user_row(int(target_id))
    t_un = (ur_t["username"] or "") if ur_t else ""
    t_disp = display_name(
        (ur_t["first_name"] or "") if ur_t else "",
        (ur_t["last_name"] or "") if ur_t else "",
        t_un,
        int(target_id)
    )
    target_tag = tg_mention(int(target_id), t_disp, username=t_un)

    a_un = getattr(actor, "username", "") or ""
    a_fn = getattr(actor, "first_name", "") or ""
    a_ln = getattr(actor, "last_name", "") or ""
    a_disp = display_name(a_fn, a_ln, a_un, attacker_id)
    organizer_tag = tg_mention(attacker_id, a_disp, username=a_un)

    def _notify(tid: int, text: str):
        return send_user_notification(int(tid), text)

    db_exec(
        "INSERT INTO sabotage_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
        "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
        (attacker_id, int(target_id), int(now + 86400)),
        commit=True
    )

    roll = random.random() * 100.0
    success = (roll < p and p > 0.0)

    if success:
        rp = int(t["rp"] or 0)
        rv = int(t["rv"] or 0)
        npi = int(t["npi"] or 0)
        nvi = int(t["nvi"] or 0)

        lost_p = rp // 2
        lost_v = rv // 2

        add_p = npi // 2 if npi > 0 else 0
        add_v = nvi // 2 if nvi > 0 else 0

        new_rp = max(0, rp - lost_p)
        new_rv = max(0, rv - lost_v)
        new_npi = npi + add_p
        new_nvi = nvi + add_v

        tgt_ar = int(t["ar"] or 0)
        tgt_am = int(t["am"] or 0)
        tgt_br = int(t["br"] or 0)

        reward_kind, reward_amount = _sabotage_reward_from_target(tgt_ar, tgt_am)
        reward_text = _sabotage_reward_text(reward_kind, reward_amount)

        down_row = db_one(
            "SELECT "
            "COALESCE(infectivity,1) AS infectivity, "
            "COALESCE(lethality,1) AS lethality, "
            "COALESCE(heaviness,1) AS heaviness, "
            "COALESCE(immunity,1) AS immunity, "
            "COALESCE(reaction,1) AS reaction, "
            "COALESCE(ids,1) AS ids, "
            "COALESCE(ips,1) AS ips, "
            "COALESCE(synthesis,1) AS synthesis, "
            "COALESCE(acceleration,1) AS acceleration, "
            "COALESCE(total_pathogens,1) AS total_pathogens, "
            "COALESCE(total_vaccines,1) AS total_vaccines "
            "FROM labs WHERE user_id=?",
            (int(target_id),)
        )

        downgrade_candidates = []
        if down_row:
            for code in SABOTAGE_DOWNGRADE_CODES:
                info = SKILLS.get(code) or {}
                col = str(info.get("col") or "").strip()
                if not col:
                    continue
                cur_lvl = max(1, int(down_row[col] or 1))
                if cur_lvl > 1:
                    downgrade_candidates.append(code)

        downgraded_code = random.choice(downgrade_candidates) if downgrade_candidates else ""
        downgraded_label = ""
        downgraded_old = 1
        downgraded_new = 1

        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")

                c.execute(
                    "UPDATE labs SET ready_pathogens=?, ready_vaccines=?, next_pathogen_in=?, next_vaccine_in=? "
                    "WHERE user_id=?",
                    (new_rp, new_rv, new_npi, new_nvi, int(target_id))
                )

                if reward_kind == "mat":
                    c.execute(
                        "UPDATE labs SET all_bio_mater=CASE "
                        "WHEN COALESCE(all_bio_mater,0) >= ? THEN all_bio_mater-? ELSE 0 END "
                        "WHERE user_id=?",
                        (int(reward_amount), int(reward_amount), int(target_id))
                    )
                    c.execute(
                        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+? "
                        "WHERE user_id=?",
                        (int(reward_amount), int(attacker_id))
                    )

                elif reward_kind == "res":
                    c.execute(
                        "UPDATE labs SET "
                        "all_bio_res=CASE WHEN COALESCE(all_bio_res,0) >= ? THEN all_bio_res-? ELSE 0 END, "
                        "bio_res=CASE WHEN COALESCE(bio_res,0) >= ? THEN bio_res-? ELSE 0 END "
                        "WHERE user_id=?",
                        (int(reward_amount), int(reward_amount), int(reward_amount), int(reward_amount), int(target_id))
                    )
                    c.execute(
                        "UPDATE labs SET "
                        "all_bio_res=COALESCE(all_bio_res,0)+?, "
                        "bio_res=COALESCE(bio_res,0)+? "
                        "WHERE user_id=?",
                        (int(reward_amount), int(reward_amount), int(attacker_id))
                    )

                else:
                    c.execute(
                        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+1 "
                        "WHERE user_id=?",
                        (int(attacker_id),)
                    )

                if downgraded_code:
                    info = SKILLS.get(downgraded_code) or {}
                    col = str(info.get("col") or "").strip()
                    downgraded_label = str(info.get("title_2") or col or "параметр").strip()
                    downgraded_old = max(1, int(down_row[col] or 1))
                    downgraded_new = max(1, int(downgraded_old - 1))

                    if downgraded_code == "PAT":
                        c.execute(
                            "UPDATE labs SET total_pathogens=?, ready_pathogens=? WHERE user_id=?",
                            (int(downgraded_new), int(min(new_rp, downgraded_new)), int(target_id))
                        )
                    elif downgraded_code == "VAC":
                        c.execute(
                            "UPDATE labs SET total_vaccines=?, ready_vaccines=? WHERE user_id=?",
                            (int(downgraded_new), int(min(new_rv, downgraded_new)), int(target_id))
                        )
                    else:
                        c.execute(
                            f"UPDATE labs SET {col}=? WHERE user_id=?",
                            (int(downgraded_new), int(target_id))
                        )

                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        if downgraded_code:
            _recalc_derived(int(target_id))

        downgrade_line_target = ""
        downgrade_line_ids = ""
        downgrade_line_actor = ""
        if downgraded_code:
            downgrade_line_target = f"\n📉 Понижен параметр: {downgraded_label} ({downgraded_old} → {downgraded_new})"
            downgrade_line_ids = f"\n📉 Понижен параметр: {downgraded_label} ({downgraded_old} → {downgraded_new})"
            downgrade_line_actor = f"\n📉 Понижен параметр цели: {downgraded_label} ({downgraded_old} → {downgraded_new})"

        tgt_notice = (
            "💥 В вашу лабораторию совершена диверсия. Марадёры повредили контейнеры с образцами и лабораторное оборудование.\n\n"
            f"🧪 Потеряно патогенов: {lost_p}\n"
            f"💉 Потеряно вакцин: {lost_v}\n"
            f"⏱️ Задержка производства: патоген +{_format_hms(add_p)} | вакцина +{_format_hms(add_v)}\n"
            f"💰 Похищено диверсантом: {reward_text}"
            f"{downgrade_line_target}\n"
            "Организатор диверсии остался неизвестен."
        )
        _notify(int(target_id), tgt_notice)

        if ids_should_fire(a_ids, t_ids):
            ids_text = render_ids_report(
                target_id=int(target_id),
                attempts=1,
                kind="sabotage",
                organizer_tag=organizer_tag,
                result_text=(
                    f"💥 Диверсия нанесла ущерб лаборатории.\n"
                    f"🧪 Потеряно патогенов: {lost_p}\n"
                    f"💉 Потеряно вакцин: {lost_v}\n"
                    f"💰 Похищено: {reward_text}"
                    f"{downgrade_line_ids}"
                )
            )
            ids_msg = _notify(int(target_id), ids_text)
            if ids_msg:
                autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")

        _emit(
            "🥷 Диверсия выполнена.\n"
            f"Цель: «{target_tag}»\n"
            f"✅ Успех ({_fmt_pct_text(p)})\n"
            f"🧪 Уничтожено патогенов: {lost_p}\n"
            f"💉 Уничтожено вакцин: {lost_v}\n"
            f"💰 Добыча: {reward_text}"
            f"{downgrade_line_actor}\n"
            "⏱️ КД на цель: 24 часа"
        )
        return

    tp = int(t["tp"] or 1) or 1
    tv = int(t["tv"] or 1) or 1

    cost_pat = _upgrade_cost(SKILL_N1["PAT"], tp, 2)
    cost_vac = _upgrade_cost(SKILL_N1["VAC"], tv, 2)
    damage = int(cost_pat + cost_vac)

    arow = db_one(
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m, COALESCE(bio_res,0) AS br "
        "FROM labs WHERE user_id=?",
        (attacker_id,)
    )
    have_r = int(arow["r"] if arow else 0)
    have_m = int(arow["m"] if arow else 0)
    have_br = int(arow["br"] if arow else 0)

    spent_r = min(have_r, damage)
    spent_m = damage - spent_r

    new_ar = have_r - spent_r
    if new_ar < 0:
        new_ar = 0
    new_am = have_m - spent_m 

    tgt_ar = int(t["ar"] or 0)
    tgt_am = int(t["am"] or 0)
    tgt_br = int(t["br"] or 0)

    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute("BEGIN")

            c.execute(
                "UPDATE labs SET all_bio_res=?, all_bio_mater=?, bio_res=? WHERE user_id=?",
                (int(new_ar), int(new_am), int(max(0, have_br - spent_r)), attacker_id)
            )

            c.execute(
                "UPDATE labs SET all_bio_res=all_bio_res+?, all_bio_mater=all_bio_mater+?, bio_res=bio_res+? WHERE user_id=?",
                (int(spent_r), int(spent_m), int(spent_r), int(target_id))
            )

            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            try:
                c.close()
            except Exception:
                pass

    spent_txt = (
        _fmt_bio_res(int(spent_r))
        if spent_m <= 0
        else f"{_fmt_bio_res(int(spent_r))} + {_fmt_bio_mater(int(spent_m))}"
    )

    tgt_notice = (
        f"📟 Попытка диверсии лаборатории «{target_tag}» была предотвращена. Группа человек была поймана на месте и дала показания.\n\n"
        f"Организатор: {organizer_tag}\n"
        f"🧾 Финансовая компенсация: {spent_txt}"
    )
    _notify(int(target_id), tgt_notice)

    if ids_should_fire(a_ids, t_ids):
        ids_text = render_ids_report(
            target_id=int(target_id),
            attempts=1,
            kind="sabotage",
            organizer_tag=organizer_tag,
            result_text=(
                "📟 Попытка вторжения была предотвращена.\n"
                f"Компенсация: {spent_txt}"
            )
        )
        ids_msg = _notify(int(target_id), ids_text)
        if ids_msg:
            autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")

    _emit(
        "🥷 Диверсия провалилась.\n"
        f"Цель: «{target_tag}»\n"
        f"❌ Неудача ({_fmt_pct_text(fail_p)})\n"
        f"🧾 Компенсация ущерба: {spent_txt}\n"
        "⏱️ КД на цель: 24 часа"
    )

def handle_lab_commands(message, parsed: Parsed):
    uid = message.from_user.id
    upsert_user(message.from_user)
    ensure_creator_is_support()

    if parsed.cmd not in (
        "lab_delete", "lab_delete_now", "restore_lab", "lab_delete_confirm_phrase",
        "labname_clear", "pathogenname_clear",
        "chatname_set", "chatname_show", "chatname_clear"
    ):
        ensure_lab_exists(uid)

    if parsed.cmd == "lab_delete":
        if not is_lab_active(int(uid)):
            bot.reply_to(
                message,
                build_inactive_lab_text(int(uid), after_delete=False),
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=kb_inactive_lab_actions(int(uid))
            )
            return

        set_lab_delete_pending(int(uid))
        bot.reply_to(
            message,
            build_lab_delete_confirm_text(),
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_lab_delete_confirm(int(uid))
        )
        return

    if parsed.cmd == "lab_delete_now":
        clear_lab_delete_pending(int(uid))

        if not is_lab_active(int(uid)):
            bot.reply_to(
                message,
                build_inactive_lab_text(int(uid), after_delete=False),
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=kb_inactive_lab_actions(int(uid))
            )
            return

        ok, text = _perform_lab_delete(int(uid))
        rm = kb_inactive_lab_actions(int(uid)) if ok else None
        out_text = build_inactive_lab_text(int(uid), after_delete=True) if ok else text

        bot.reply_to(
            message,
            out_text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=rm
        )
        return

    if parsed.cmd == "lab_delete_confirm_phrase":
        if not has_lab_delete_pending(int(uid)):
            return

        ok, text = _perform_lab_delete(int(uid))
        rm = kb_inactive_lab_actions(int(uid)) if ok else None
        out_text = build_inactive_lab_text(int(uid), after_delete=True) if ok else text

        bot.reply_to(
            message,
            out_text,
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=rm
        )
        return

    if parsed.cmd == "restore_lab":
        ok, text = _restore_deleted_lab(int(uid), support_mode=False)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd in ("chatname_set", "chatname_show", "chatname_clear"):
        chat_id = int(message.chat.id)
        me_row = get_user_row(int(uid))
        me_un = (
            (me_row["username"] or "").strip()
            if me_row else
            ((getattr(message.from_user, "username", None) or "").strip())
        )

        if parsed.cmd == "chatname_set":
            new_name = _normalize_chat_user_name(parsed.args or "")
            lock_row = get_name_restriction_row(int(uid))
            if lock_row and int(lock_row["user_locked"] or 0) == 1:
                bot.reply_to(message, "📑 Возможность менять имя пользователя в чатах ограничена. Обратитесь к агенту тех.поддержки.")
                return
            if not new_name:
                return
            if len(new_name) > _CHAT_USER_NAME_MAX_LEN:
                bot.reply_to(message, f"📑 Ник превышает максимальные {_CHAT_USER_NAME_MAX_LEN} символов.")
                return
            if _chat_user_name_is_invalid(new_name):
                bot.reply_to(message, "📑 Найдены недопустимые символы. Повторите попытку.")
                return

            set_chat_user_name(chat_id, int(uid), new_name)
            bot.reply_to(
                message,
                f"✅ Ник {standard_user_tag(int(uid))} изменён на «{tg_mention(int(uid), new_name, username=me_un)}»",
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return

        if parsed.cmd == "chatname_clear":
            clear_chat_user_name(chat_id, int(uid))
            bot.reply_to(
                message,
                f"❎ Ник {standard_user_tag(int(uid))} удалён.",
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)

        if target_id is None:
            if not (parsed.args or "").strip() and not getattr(message, "reply_to_message", None):
                target_id = int(uid)
                target_user_obj = message.from_user
            else:
                bot.reply_to(message, "📑 Укажите пользователя через @username, user_id, ссылку или reply.")
                return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        row = get_user_row(int(target_id))
        un = (row["username"] or "").strip() if row else ""
        current_chat_name = get_chat_user_name(chat_id, int(target_id))

        if current_chat_name:
            shown_name = current_chat_name
        elif row:
            shown_name = standard_display_name(
                row["first_name"] or "",
                row["last_name"] or "",
                row["username"] or "",
                int(target_id)
            )
        else:
            disp, _, _ = _best_known_display_by_uid(int(target_id))
            shown_name = disp

        shown_tag = tg_mention(int(target_id), shown_name, username=un)
        bot.reply_to(
            message,
            f"📋 Ник {standard_user_tag(int(target_id))}: «{shown_tag}»",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd in ("labname_clear", "pathogenname_clear"):
        targeting_other = bool((parsed.args or "").strip()) or bool(message.reply_to_message)

        if targeting_other and not is_support(int(uid)):
            bot.reply_to(message, "📑 Эта команда доступна только агентам техподдержки.")
            return

        if targeting_other:
            target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
            tok = (parsed.args.split()[0] if parsed.args else "")

            if is_bot_target(target_id, target_user_obj, tok):
                bot.reply_to(message, bot_cannot_have("имени лаборатории или патогена"))
                return

            if target_id is None:
                bot.reply_to(message, "📑 Укажите пользователя через @username, user_id или reply.")
                return

            if target_user_obj is not None:
                capture_user_context(message, target_user_obj)
        else:
            target_id = int(uid)

        ensure_lab_exists(int(target_id))

        if parsed.cmd == "labname_clear":
            set_lab_name(int(target_id), None)
            default_name = default_lab_name(get_user_row(int(target_id)), int(target_id))

            if int(target_id) == int(uid):
                bot.reply_to(
                    message,
                    f"✅ Имя лаборатории удалено.",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            else:
                bot.reply_to(
                    message,
                    f"✅ Имя лаборатории у пользователя {_corp_actor_tag(int(target_id))} удалено.",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            return

        set_pathogen_name(int(target_id), None)
        if int(target_id) == int(uid):
            bot.reply_to(message, "✅ Имя патогена удалено.", parse_mode="HTML")
        else:
            bot.reply_to(
                message,
                f"✅ Имя патогена у пользователя {_corp_actor_tag(int(target_id))} удалено.",
                parse_mode="HTML",
                disable_web_page_preview=True
            )
        return

    if parsed.cmd == "labname":
        if not parsed.args:
            lab = get_lab(uid)
            current = (lab["lab_name"] or "").strip()
            if not current:
                current = default_lab_name(get_user_row(uid), uid)
            bot.reply_to(message, f"🏢 Текущее имя лаборатории: <b>{h(current)}</b>\nЧтобы изменить его, введите:\n <code>Био имя имя лаборатории Название</code>")
            return

        new_name = re.sub(r"\s+", " ", parsed.args.strip())
        lock_row = get_name_restriction_row(int(uid))
        if lock_row and int(lock_row["lab_locked"] or 0) == 1:
            bot.reply_to(message, "📑 Возможность менять имя лаборатории ограничена. Обратитесь к агенту тех.поддержки.")
            return
        if len(new_name) > 40:
            bot.reply_to(message, "📑 Название вашей лаборатории превышает максимальные 40 символов.")
            return
        if is_lab_name_taken(new_name, exclude_user_id=int(uid)):
            bot.reply_to(message, "📑 Это имя лаборатории уже занято другим пользователем.")
            return

        set_lab_name(uid, new_name)
        bot.reply_to(message, f"✅ Имя лаборатории успешно изменено на {h(new_name)}!")
        return

    if parsed.cmd == "pathogenname":
        if not parsed.args:
            lab = get_lab(uid)
            current = (lab["pathogen_name"] or "").strip() or "неизвестный патоген"
            bot.reply_to(message, f"🦠 Текущее имя патогена: <b>{h(current)}</b>\nЧтобы изменить его, введите:\n <code>Био имя патогена Название</code>")
            return

        new_name = re.sub(r"\s+", " ", parsed.args.strip())
        lock_row = get_name_restriction_row(int(uid))
        if lock_row and int(lock_row["pat_locked"] or 0) == 1:
            bot.reply_to(message, "📑 Возможность менять имя патогена ограничена. Обратитесь к агенту тех.поддержки.")
            return
        if len(new_name) > 40:
            bot.reply_to(message, "📑 Название вашего патогена превышает максимальные 40 символов.")
            return
        if is_pathogen_name_taken(new_name, exclude_user_id=int(uid)):
            bot.reply_to(message, "📑 Это имя патогена уже занято другим пользователем.")
            return

        set_pathogen_name(uid, new_name)
        bot.reply_to(message, f"✅ Имя патогена успешно изменено на {h(new_name)}!")
        return

    if parsed.cmd == "pathogens_info":
        pref_args = (parsed.args or "").strip()
        if pref_args:
            mode, chat_filter, err = _parse_quick_infect_pref_args(pref_args)
            if err:
                bot.reply_to(message, err, parse_mode="HTML", disable_web_page_preview=True)
                return

            if mode == "c" and message.chat.type not in ("group", "supergroup"):
                bot.reply_to(
                    message,
                    "📑 Режим <code>чат</code> нельзя использовать в личных сообщениях бота.",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
                return

            set_quick_infect_pref(int(uid), mode, chat_filter)

        bot.reply_to(
            message,
            render_pathogens_info(int(uid)),
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_pathogens(int(uid))
        )
        return

    if parsed.cmd == "pathogen_info":
        bot.reply_to(
            message,
            render_pathogen_brief(int(uid)),
            parse_mode="HTML",
            disable_web_page_preview=True,
            reply_markup=kb_pathogen_info(int(uid))
        )
        return

    if parsed.cmd in ("lab", "mylab"):
        _merge_placeholder_to_real_user(message.from_user)

        if parsed.cmd == "mylab":
            target_id = int(uid)
            target_user_obj = message.from_user
        else:
            target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)

        if target_id is None and parsed.args:
            bot.reply_to(message, "📑 Этот пользователь ещё не создал свою лабораторию.")
            return

        if target_id is None:
            target_id = int(uid)
            target_user_obj = message.from_user

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        if int(target_id) == int(uid) and not is_lab_active(int(uid)):
            bot.reply_to(
                message,
                build_inactive_lab_text(int(uid), after_delete=False),
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=kb_inactive_lab_actions(int(uid))
            )
            return
        
        tok = (parsed.args.split()[0] if parsed.args else "")
        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("лаборатории"))
            return        

        if int(target_id) != int(uid):
            if not is_lab_active(int(target_id)):
                bot.reply_to(message, "📑 Этот пользователь ещё не создал свою лабораторию.")
                return
        ensure_lab_exists(target_id)

        if int(target_id) == int(uid):
            _hb, hl = get_privacy_flags(int(uid))
            text = render_lab(target_id)
            rm = kb_lab_dossier(int(target_id))

            if message.chat.type in ("group", "supergroup") and hl == 1:
                sent = _send_hidden_self_info_to_pm(int(uid), text, reply_markup=rm)
                if sent:
                    bot.reply_to(
                        message,
                        "📋 Информация о вашей лаборатории отправлена в личные сообщения.",
                        reply_markup=kb_open_bot_pm()
                    )
                else:
                    bot.reply_to(
                        message,
                        "📑 Не удалось отправить информацию в личные сообщения. Сначала откройте личный чат с ботом.",
                        reply_markup=kb_open_bot_pm()
                    )
                return

            bot.reply_to(
                message,
                text,
                disable_web_page_preview=True,
                reply_markup=rm
            )
            return

        _hb, hl = get_privacy_flags(int(target_id))
        if hl == 1 and not same_corp(int(uid), int(target_id)):
            bot.reply_to(message, "🔒 Досье лаборатории скрыто пользователем.")
            return
        bot.reply_to(message, render_lab(target_id), disable_web_page_preview=True)
        return

def handle_corp_commands(message, parsed: Parsed):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    if not is_lab_active(uid) and parsed.cmd in (
        "corp_create", "corp_delete", "corp_open", "corp_close", "corp_reg", "corp_join",
        "corp_send_res", "corp_send_mat"
    ):
        bot.reply_to(message, "📑 Сначала создайте лабораторию. Команда \"<code>Био лаб</code>\".")
        return

    my_cid, my_cname = get_user_corp_resolved(uid)

    if parsed.cmd == "corp_rename":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if int(corp["owner_id"] or 0) != int(uid):
            bot.reply_to(message, "📑 Менять название Корпорации может только её владелец.")
            return

        lock_row = get_name_restriction_row(int(uid))
        if lock_row and int(lock_row["corp_locked"] or 0) == 1:
            bot.reply_to(message, "📑 Возможность менять название Корпорации ограничена. Обратитесь к агенту тех.поддержки.")
            return

        new_name = re.sub(r"\s+", " ", (parsed.args or "").strip())
        if not new_name:
            bot.reply_to(message, "📑 Укажите новое название Корпорации.")
            return

        if len(new_name) > 40:
            bot.reply_to(message, "📑 Название Корпорации превышает максимальные 40 символов.")
            return

        ex = corp_by_name(new_name)
        if ex and int(ex["corp_id"] or 0) != int(my_cid):
            bot.reply_to(message, "📑 Корпорация с таким названием уже существует.")
            return

        try:
            with DB_LOCK:
                c = conn.cursor()
                try:
                    c.execute("BEGIN")
                    c.execute("UPDATE corps SET name=? WHERE corp_id=?", (new_name, int(my_cid)))
                    c.execute(
                        "UPDATE labs SET corp_name=? WHERE user_id IN (SELECT user_id FROM corp_members WHERE corp_id=?)",
                        (new_name, int(my_cid))
                    )
                    conn.commit()
                except Exception:
                    conn.rollback()
                    raise
                finally:
                    try:
                        c.close()
                    except Exception:
                        pass
        except Exception as e:
            send_error_report("corp_rename", e)
            bot.reply_to(message, "📑 Не удалось изменить название Корпорации.")
            return

        bot.reply_to(
            message,
            f"✅ Название Корпорации изменено на {corp_name_display(new_name)}.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "corp_create":
        if my_cid > 0:
            bot.reply_to(message, "📑 Вы уже состоите в Корпорации.")
            return

        raw_name = (parsed.args or "").strip()
        lock_row = get_name_restriction_row(int(uid))
        if lock_row and int(lock_row["corp_locked"] or 0) == 1 and raw_name:
            bot.reply_to(message, "📑 Возможность менять название Корпорации ограничена. Обратитесь к агенту тех.поддержки.")
            return

        name = raw_name
        if not name:
            u = get_user_row(uid)
            un = (u["username"] or "") if u else ""
            disp = display_name((u["first_name"] or "") if u else "", (u["last_name"] or "") if u else "", un, uid)
            name = f"им. {disp}".strip()

        if len(name) > 40:
            bot.reply_to(message, "📑 Название Корпорации превышает максимальные 40 символов.")
            return

        ex = corp_by_name(name)
        if ex:
            bot.reply_to(message, "📑 Корпорация с таким названием уже существует.")
            return

        created_chat_id = int(message.chat.id) if message.chat.type in ("group", "supergroup") else 0
        now = now_ts()

        try:
            with DB_LOCK:
                c = conn.cursor()
                try:
                    c.execute("BEGIN")
                    c.execute(
                        "INSERT INTO corps(name, owner_id, created_chat_id, created_at, is_open, min_bio_exp) "
                        "VALUES (?,?,?,?,1,0)",
                        (name, uid, created_chat_id, now)
                    )
                    corp_id = int(c.lastrowid)

                    c.execute(
                        "INSERT INTO corp_members(corp_id, user_id, role, joined_at) VALUES (?,?, 'owner', ?)",
                        (corp_id, uid, now)
                    )

                    c.execute(
                        "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                        (corp_id, name, uid)
                    )
                    conn.commit()
                except Exception:
                    conn.rollback()
                    raise
                finally:
                    try:
                        c.close()
                    except Exception:
                        pass
        except Exception as e:
            send_error_report("corp_create", e)
            bot.reply_to(message, "📑 Не удалось создать корпорацию.")
            return

        bot.reply_to(message, f"✅ Корпорация <b>{h(name)}</b> создана. Это ваш первый шаг к монополии над всем миром игры.", disable_web_page_preview=True)
        return

    if parsed.cmd == "corp_delete":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if int(corp["owner_id"]) != uid:
            bot.reply_to(message, "📑 Удалить Корпорацию может только владелец.")
            return

        members = corp_members_full(my_cid)
        corp_name = (corp["name"] or "").strip()

        with DB_LOCK:
            c = conn.cursor()
            try:
                c.execute("BEGIN")
                c.execute(
                    "UPDATE labs SET corp_id=0, corp_name='' WHERE user_id IN (SELECT user_id FROM corp_members WHERE corp_id=?)",
                    (my_cid,)
                )
                c.execute("DELETE FROM corp_members WHERE corp_id=?", (my_cid,))
                c.execute("DELETE FROM corp_invites WHERE corp_id=?", (my_cid,))
                c.execute("DELETE FROM corp_requests WHERE corp_id=?", (my_cid,))
                c.execute("DELETE FROM corp_request_msgs WHERE request_id IN (SELECT request_id FROM corp_requests WHERE corp_id=?)", (my_cid,))
                c.execute("DELETE FROM corps WHERE corp_id=?", (my_cid,))
                conn.commit()
            except Exception:
                conn.rollback()
                raise
            finally:
                try:
                    c.close()
                except Exception:
                    pass

        notice = (
            "📰 Сообщаем вам новость:\n"
            f"Корпорация {corp_name_display(corp_name)} была распущена её владельцем.\n"
            "С этого дня Вы сами-по-себе."
        )
        for m in members:
            mid = int(m["user_id"])
            if mid == uid:
                continue
            try:
                bot.send_message(mid, notice, parse_mode="HTML", disable_web_page_preview=True)
            except Exception:
                pass

        bot.reply_to(message, "✅ Корпорация распущена.", disable_web_page_preview=True)
        return

    if parsed.cmd in ("corp_open", "corp_close"):
        corp_id = int(my_cid or 0)

        if corp_id <= 0:
            r = db_one(
                "SELECT corp_id FROM corp_members WHERE user_id=? "
                "ORDER BY CASE role "
                "           WHEN 'owner' THEN 0 "
                "           WHEN 'deputy' THEN 1 "
                "           ELSE 2 "
                "         END, joined_at ASC "
                "LIMIT 1",
                (uid,)
            )
            corp_id = int(r["corp_id"] or 0) if r else 0

        if corp_id <= 0:
            bot.reply_to(message, "📑 Вы не состоите в корпорации.")
            return

        if not corp_is_owner_or_deputy(corp_id, uid):
            bot.reply_to(message, "📑 Изменять тип Корпорации могут только владелец и заместители.")
            return

        is_open = 1 if parsed.cmd == "corp_open" else 0
        db_exec("UPDATE corps SET is_open=? WHERE corp_id=?", (is_open, corp_id), commit=True)

        corp = corp_by_id(corp_id)
        if corp:
            db_exec(
                "UPDATE labs SET corp_id=?, corp_name=? WHERE user_id=?",
                (corp_id, (corp["name"] or "").strip(), uid),
                commit=True
            )

        bot.reply_to(
            message,
            f"✅ Тип корпорации изменён на: {'Открытый' if is_open == 1 else 'Закрытый'}."
        )
        return

    if parsed.cmd == "corp_reg":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return
        if not corp_is_owner_or_deputy(my_cid, uid):
            bot.reply_to(message, "📑 Изменять порог вступления могут только владелец и заместители.")
            return
        try:
            v = int((parsed.args or "").strip())
        except Exception:
            v = 0
        if v < 0:
            v = 0
        db_exec("UPDATE corps SET min_bio_exp=? WHERE corp_id=?", (v, my_cid), commit=True)
        if v == 0:
            bot.reply_to(message, "✅ Порог вступления отключён.")
        else:
            bot.reply_to(message, f"✅ Порог вступления установлен: требуемое число био-опыта {_fmt_k(v)}.")
        return

    if parsed.cmd == "corp_invite":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if corp_is_open_value(corp) == 0 and not corp_is_owner_or_deputy(my_cid, uid):
            bot.reply_to(message, "📑 В закрытом типе Корпорации приглашать новых участников могут только владелец и заместители.")
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        tok = (parsed.args.split()[0] if parsed.args else "")

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("членства в корпорации"))
            return

        if target_id is None:
            return

        if int(target_id) == int(uid):
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        if not is_lab_active(int(target_id)):
            bot.reply_to(message, "📑 Этот пользователь ещё не создал свою лабораторию.")
            return

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if tgt_cid > 0:
            bot.reply_to(message, "📑 Этот пользователь уже состоит в Корпорации.")
            return

        ex = db_one(
            "SELECT invite_id FROM corp_invites "
            "WHERE corp_id=? AND user_id=? AND status='pending' "
            "ORDER BY invite_id DESC LIMIT 1",
            (int(my_cid), int(target_id))
        )
        if ex:
            bot.reply_to(message, "📑 Этому игроку уже отправлено приглашение.")
            return

        invite_chat_id = int(target_id)
        sent_to_pm = True

        if message.chat.type in ("group", "supergroup") and _chat_has_user(int(message.chat.id), int(target_id)):
            invite_chat_id = int(message.chat.id)
            sent_to_pm = False

        try:
            _create_corp_invite(corp, int(target_id), uid, chat_id=invite_chat_id)
        except Exception as e:
            send_error_report("corp_invite_create", e)
            bot.reply_to(message, "📑 Не удалось отправить приглашение.")
            return

        if sent_to_pm:
            bot.reply_to(message, "📨 Приглашение отправлено игроку в личные сообщения.")
        return

    if parsed.cmd == "corp_deputy":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if int(corp["owner_id"]) != int(uid):
            bot.reply_to(message, "📑 Назначать заместителей может только владелец Корпорации.")
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        tok = (parsed.args.split()[0] if parsed.args else "")

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("роли заместителя корпорации"))
            return

        if target_id is None:
            return

        if int(target_id) == int(uid):
            bot.reply_to(message, "📑 Нельзя назначить заместителем самого себя.")
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if int(tgt_cid) != int(my_cid):
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        role = corp_role(int(my_cid), int(target_id))
        if role == "owner":
            bot.reply_to(message, "📑 Владелец уже обладает максимальными правами.")
            return
        if role == "deputy":
            bot.reply_to(message, "📑 Этот игрок уже является заместителем.")
            return

        db_exec(
            "UPDATE corp_members SET role='deputy' WHERE corp_id=? AND user_id=?",
            (int(my_cid), int(target_id)),
            commit=True
        )

        bot.reply_to(
            message,
            f"✅ Игрок {_corp_actor_tag(int(target_id))} {_gender_pick(int(target_id), 'corp_deputy_assign')} {corp_name_display(corp['name'])}.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "corp_deputy_remove":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if int(corp["owner_id"]) != int(uid):
            bot.reply_to(message, "📑 Снимать права заместителя может только владелец Корпорации.")
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        tok = (parsed.args.split()[0] if parsed.args else "")

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("роли заместителя корпорации"))
            return

        if target_id is None:
            return

        if int(target_id) == int(uid):
            bot.reply_to(message, "📑 Вы не можете разжаловать самого себя")
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if int(tgt_cid) != int(my_cid):
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        role = corp_role(int(my_cid), int(target_id))
        if role != "deputy":
            bot.reply_to(message, "📑 Этот игрок не является заместителем Корпорации.")
            return

        db_exec(
            "UPDATE corp_members SET role='member' WHERE corp_id=? AND user_id=?",
            (int(my_cid), int(target_id)),
            commit=True
        )
        
        bot.reply_to(
            message,
            f"✅ Игрок {_corp_actor_tag(int(target_id))} {_gender_pick(int(target_id), 'corp_deputy_remove')} {corp_name_display(corp['name'])}.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "corp_kick":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if not corp_is_owner_or_deputy(my_cid, uid):
            bot.reply_to(message, "📑 Исключать участников могут только владелец и заместители.")
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        tok = (parsed.args.split()[0] if parsed.args else "")

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("членства в корпорации"))
            return

        if target_id is None:
            return

        if int(target_id) == int(uid):
            bot.reply_to(message, "📑 Нельзя исключить самого себя. Используйте команду \"<code>Био покинуть</code>\".", parse_mode="HTML", disable_web_page_preview=True)
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if int(tgt_cid) != int(my_cid):
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        role = corp_role(int(my_cid), int(target_id))
        if role == "owner":
            bot.reply_to(message, "📑 Нельзя исключить владельца Корпорации.")
            return
        if not role:
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        try:
            _corp_remove_member(int(my_cid), int(target_id))
            _corp_notify_kicked(int(target_id), corp)
        except Exception as e:
            send_error_report("corp_kick", e)
            bot.reply_to(message, "📑 Не удалось исключить игрока из Корпорации.")
            return

        bot.reply_to(
            message,
            f"✅ Игрок {_corp_actor_tag(int(target_id))} {_gender_pick(int(target_id), 'corp_kick_public')}.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd == "corp_leave":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        role = corp_role(int(my_cid), int(uid))
        if role == "owner":
            bot.reply_to(message, "📑 Владелец не может покинуть свою Корпорацию.")
            return

        try:
            _corp_remove_member(int(my_cid), int(uid))
            _corp_notify_leave(int(my_cid), int(uid))
        except Exception as e:
            send_error_report("corp_leave", e)
            bot.reply_to(message, "📑 Не удалось покинуть Корпорацию.")
            return

        bot.reply_to(message, f"✅ Вы покинули Корпорацию {corp_name_display(corp['name'])}")
        return

    if parsed.cmd == "corp_transfer_owner":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if int(corp["owner_id"]) != int(uid):
            bot.reply_to(message, "📑 Передавать права владельца может только текущий владелец Корпорации.")
            return

        target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
        tok = (parsed.args.split()[0] if parsed.args else "")

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("прав владельца корпорации"))
            return

        if target_id is None:
            target_id = _corp_pick_new_owner_target(int(my_cid), int(uid))
            target_user_obj = None

        if int(target_id or 0) <= 0:
            bot.reply_to(message, "📑 В вашей Корпорации некому передавать права владельца.")
            return

        if int(target_id) == int(uid):
            bot.reply_to(message, "📑 Нельзя передать права владельца самому себе.")
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if int(tgt_cid) != int(my_cid):
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        role = corp_role(int(my_cid), int(target_id))
        if not role:
            bot.reply_to(message, "📑 Этот игрок не состоит в вашей Корпорации.")
            return

        try:
            _corp_transfer_owner_rights(int(my_cid), int(uid), int(target_id))
        except Exception as e:
            send_error_report("corp_transfer_owner", e)
            bot.reply_to(message, "📑 Не удалось передать права владельца.")
            return

        try:
            bot.send_message(
                int(target_id),
                f"📄 Вам переданы права владельца Корпорации {corp_name_display(corp['name'])}.",
                parse_mode="HTML",
                disable_web_page_preview=True
            )
        except Exception:
            pass

        bot.reply_to(
            message,
            f"✅ Права владельца Корпорации {corp_name_display(corp['name'])} переданы игроку {_corp_actor_tag(int(target_id))}. Приветствуйте нового Босса.",
            parse_mode="HTML",
            disable_web_page_preview=True
        )
        return

    if parsed.cmd in ("corp_send_res", "corp_send_mat"):
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        amount, target_id, target_user_obj, tok = _parse_corp_transfer_args(message, parsed)
        if amount <= 0:
            bot.reply_to(message, "📑 Укажите корректное число для перевода.")
            return

        if is_bot_target(target_id, target_user_obj, tok):
            bot.reply_to(message, bot_cannot_have("корпоративного перевода"))
            return

        if target_id is None:
            bot.reply_to(message, "📑 Укажите, кому вы переводите био-материалы или био-ресурсы.")
            return

        if int(target_id) == int(uid):
            bot.reply_to(message, "📑 Нет смысла передавать средства самому себе.")
            return

        if target_user_obj is not None:
            capture_user_context(message, target_user_obj)

        tgt_cid, _ = get_user_corp_resolved(int(target_id))
        if int(tgt_cid) != int(my_cid):
            bot.reply_to(message, "📑 Переводить ресурсы и материалы можно только участникам своей Корпорации.")
            return

        try:
            cmd = str(parsed.cmd or "").strip()
            plan = _corp_transfer_plan(int(uid), cmd, int(amount))

            if not bool(plan.get("ok")):
                set_balance_chain_state_from_message(
                    message,
                    BALCHAIN_CORP_TRANSFER,
                    "Повторить перевод",
                    {"cmd": cmd, "amount": int(amount), "target_id": int(target_id)}
                )
                bot.reply_to(
                    message,
                    _corp_transfer_shortage_error(cmd),
                    reply_markup=kb_open_balance(int(uid))
                )
                return

            if bool(plan.get("mixed")) or bool(plan.get("substitute_only")):
                bot.reply_to(
                    message,
                    _corp_transfer_mix_text(
                        cmd,
                        int(target_id),
                        int(plan["res_amount"]),
                        int(plan["mat_amount"])
                    ),
                    parse_mode="HTML",
                    disable_web_page_preview=True,
                    reply_markup=kb_corp_transfer_mix_offer(
                        int(uid),
                        cmd,
                        int(target_id),
                        int(plan["res_amount"]),
                        int(plan["mat_amount"])
                    )
                )
                return

            ok, err = _corp_transfer_apply(
                int(uid),
                int(target_id),
                res_amount=int(plan["res_amount"]),
                mat_amount=int(plan["mat_amount"])
            )
            if not ok:
                if err in ("📝 У вас нет столько био-ресурсов.", "📝 У вас нет столько био-материалов."):
                    set_balance_chain_state_from_message(
                        message,
                        BALCHAIN_CORP_TRANSFER,
                        "Повторить перевод",
                        {"cmd": cmd, "amount": int(amount), "target_id": int(target_id)}
                    )
                    bot.reply_to(message, err, reply_markup=kb_open_balance(int(uid)))
                else:
                    bot.reply_to(message, err)
                return

            st = get_balance_chain_state(int(uid))
            if st and str(st.get("chain_kind") or "") == BALCHAIN_CORP_TRANSFER:
                clear_balance_chain_state(int(uid))

            bot.reply_to(
                message,
                _corp_transfer_success_text(
                    int(target_id),
                    int(plan["res_amount"]),
                    int(plan["mat_amount"])
                ),
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return

        except Exception as e:
            send_error_report("corp_transfer", e)
            bot.reply_to(message, "❌ Не удалось выполнить перевод.")
            return

    if parsed.cmd == "corp_join":
        if my_cid > 0:
            bot.reply_to(message, "📑 Вы уже состоите в Корпорации.")
            return

        corp = resolve_corp_for_join(message, parsed)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        min_be = int(corp["min_bio_exp"] or 0)
        my_lab = get_lab(uid)
        my_be = int(my_lab["bio_exp"] or 0)
        if min_be > 0 and my_be < min_be:
            bot.reply_to(message, f"📑 Для вступления требуется как минимум био-опыта {_fmt_k(min_be)}.")
            return

        corp_id = int(corp["corp_id"])

        if corp_is_open_value(corp) == 1:
            try:
                _corp_join_open(uid, corp)
                _send_corp_join_notices(corp, uid)
            except Exception as e:
                send_error_report("corp_join_open", e)
                bot.reply_to(message, "📑 Не удалось вступить в Корпорацию.")
                return

            who = _corp_actor_tag(uid)
            bot.reply_to(
                message,
                f"✅ Вы приняты в Корпорацию {corp_name_display(corp['name'])}\n"
                f"Добро пожаловать в коллектив, {who}",
                parse_mode="HTML",
                disable_web_page_preview=True
            )
            return

        ex = db_one(
            "SELECT request_id FROM corp_requests WHERE corp_id=? AND user_id=? AND status='pending' ORDER BY request_id DESC LIMIT 1",
            (corp_id, uid)
        )
        if ex:
            bot.reply_to(message, "📑 Ваша заявка уже находится на рассмотрении.")
            return

        try:
            _create_corp_request(
                corp,
                uid,
                user_chat_id=int(message.chat.id),
                user_reply_to=int(message.message_id)
            )
        except Exception as e:
            send_error_report("corp_join_request", e)
            bot.reply_to(message, "📑 Не удалось отправить заявку на вступление.")
            return

        return

    if parsed.cmd in ("corp_req_accept", "corp_req_reject"):
        if message.chat.type != "private":
            bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
            return

        request_id = _resolve_request_id_from_message_or_args(message, parsed)
        if request_id <= 0:
            bot.reply_to(message, "📑 Ответьте на сообщение с заявкой или укажите ID заявки.")
            return

        approved = (parsed.cmd == "corp_req_accept")
        try:
            ok, msg = _corp_request_resolve(int(request_id), uid, approved)
        except Exception as e:
            send_error_report("corp_req_text_resolve", e)
            bot.reply_to(message, "📑 Не удалось обработать заявку.")
            return

        bot.reply_to(message, msg)
        return

    if parsed.cmd in ("corp_info", "corp_my"):
        name = (parsed.args or "").strip()
        corp = None

        if parsed.cmd == "corp_my":
            if my_cid <= 0:
                bot.reply_to(
                    message,
                    "📑 Вы не состоите ни в одной Корпорации.\n"
                    "Команда вступления \"<code>Био вступить</code> + название Корпорации\"",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
                return
            corp = corp_by_id(my_cid)

        if corp is None and parsed.cmd == "corp_info":
            target_id, target_user_obj = resolve_target_from_reply_or_args(message, parsed)
            if target_id is not None:
                if target_user_obj is not None:
                    capture_user_context(message, target_user_obj)

                if _is_game_bot_target(int(target_id), target_user_obj):
                    bot.reply_to(
                        message,
                        "📑 Как бы вам и мне не хотелось, но бот не может участвовать в игре. Бот не может состоять в корпорации."
                    )
                    return

                rcid, _ = get_user_corp_resolved(int(target_id))
                if rcid > 0:
                    corp = corp_by_id(int(rcid))
                else:
                    bot.reply_to(message, "📑 Этот пользователь не состоит в Корпорации.")
                    return

        if corp is None and not name and _reply_is_direct_bot_without_targets(message, uid):
            bot.reply_to(
                message,
                "📑 Как бы вам и мне не хотелось, но бот не может участвовать в игре. Бот не может состоять в корпорации."
            )
            return

        if corp is None and not name and message.reply_to_message and getattr(message.reply_to_message, "from_user", None):
            ru = message.reply_to_message.from_user
            if not bool(getattr(ru, "is_bot", False)):
                rcid, _ = get_user_corp_resolved(int(ru.id))
                if rcid > 0:
                    corp = corp_by_id(int(rcid))
                else:
                    bot.reply_to(message, "📑 Этот пользователь не состоит в Корпорации.")
                    return

        if corp is None:
            if not name:
                if my_cid <= 0:
                    return
                corp = corp_by_id(my_cid)
            else:
                corp = corp_by_name(name)

        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        viewer_id = uid
        text, rm = render_corp_info_text(corp, viewer_id)

        is_open = corp_is_open_value(corp)
        if not corp_is_member(int(corp["corp_id"]), viewer_id) and is_open == 0:
            nm = (corp["name"] or "").strip()
            text = (
                f"🔒 Досье Корпорации {corp_name_display(nm)} недоступно для посторонних.\n"
                f"Подайте заявку на вступление, команда \"<code>Био вступить {h(nm)}</code>\""
            )
            rm = kb_corp_info(int(corp["corp_id"]), viewer_id, False)

        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return
    
    if parsed.cmd == "corp_req_list":
        if my_cid <= 0:
            bot.reply_to(message, "📑 Вы не состоите в Корпорации.")
            return

        corp = corp_by_id(my_cid)
        if not corp:
            bot.reply_to(message, "📑 Корпорация не найдена.")
            return

        if not corp_is_owner_or_deputy(int(my_cid), int(uid)):
            bot.reply_to(message, "📑 Просматривать активные заявки могут только владелец и заместители Корпорации.")
            return

        text, rm = render_corp_requests_text(corp, uid)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

# INLINE MODE
def _inline_strip_target_prefix(query: str) -> tuple[Optional[int], str, str]:
    raw = (query or "").strip()
    if not raw:
        return None, "", ""

    parts = raw.split(None, 1)
    tok = parts[0].strip()
    tail = parts[1].strip() if len(parts) > 1 else ""

    tid = _resolve_or_create_infect_target(tok)
    if tid is not None:
        return int(tid), tok, tail

    return None, "", raw

def _inline_wants_lab(q: str) -> bool:
    low = (q or "").strip().lower()
    return (not low) or low in (
        "лаб", "лаба", "лаборатория", "моя лаба", "моя лаборатория",
        "досье", "досье лаборатории"
    ) or low.startswith(("лаб", "лабо", "моя л", "досье лаб", "досье"))

def _inline_wants_balance(q: str) -> bool:
    low = (q or "").strip().lower()
    return (not low) or low in (
        "баланс", "мешок", "кошелек", "кошелёк", "кош", "бал", "меш"
    ) or low.startswith(("бал", "меш", "кош"))

def _inline_wants_corp(q: str) -> bool:
    low = (q or "").strip().lower()
    return (not low) or low in (
        "корп", "корпорация", "корпа", "моя корп", "моя корпорация", "досье корпорации"
    ) or low.startswith(("корп", "моя к", "досье корп"))

def _render_inline_balance_for_viewer(viewer_id: int, target_id: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    ensure_lab_exists(int(target_id))

    if int(target_id) == int(viewer_id):
        return render_balance(int(target_id)), kb_balance_self(int(viewer_id))

    hb, _hl = get_privacy_flags(int(target_id))
    if hb == 1 and not same_corp(int(viewer_id), int(target_id)):
        return "🔒 Баланс скрыт пользователем.", None

    return render_balance(int(target_id)), None

def _render_inline_lab_for_viewer(viewer_id: int, target_id: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    if int(target_id) != int(viewer_id) and not is_lab_active(int(target_id)):
        return "📑 Этот пользователь ещё не создал свою лабораторию.", None

    ensure_lab_exists(int(target_id))

    if int(target_id) == int(viewer_id):
        return render_lab(int(target_id)), kb_lab_dossier_inline(int(target_id))

    _hb, hl = get_privacy_flags(int(target_id))
    if hl == 1 and not same_corp(int(viewer_id), int(target_id)):
        return "🔒 Досье лаборатории скрыто пользователем.", None

    return render_lab(int(target_id)), None

def _render_inline_corp_for_viewer(viewer_id: int, target_id: int) -> tuple[str, Optional[InlineKeyboardMarkup]]:
    cid, _ = get_user_corp_resolved(int(target_id))
    if int(cid) <= 0:
        return "📑 Этот пользователь не состоит в Корпорации.", None

    corp = corp_by_id(int(cid))
    if not corp:
        return "📑 Корпорация не найдена.", None

    text, rm = render_corp_info_text(corp, int(viewer_id))
    if not corp_is_member(int(corp["corp_id"]), int(viewer_id)) and corp_is_open_value(corp) == 0:
        nm = (corp["name"] or "").strip()
        text = (
            f"🔒 Досье Корпорации {corp_name_display(nm)} недоступно для посторонних.\n"
            f"Подайте заявку на вступление, команда \"<code>Био вступить {h(nm)}</code>\""
        )
        rm = kb_corp_info(int(corp["corp_id"]), int(viewer_id), False)

    return text, rm

def kb_inline_infect_execute_user(attacker_id: int, target_id: int, count: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(_ikb("Заразить", callback_data=f"{INFUI_TAG}:U:{int(attacker_id)}:{int(target_id)}:{int(count)}", style="success"))
    return kb

def kb_inline_infect_execute_mass(attacker_id: int, mode: str, count: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(_ikb("Заразить", callback_data=f"{INFUI_TAG}:M:{int(attacker_id)}:{str(mode)}:n:{int(count)}", style="success"))
    return kb

def kb_inline_rp_offer(offer_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb("Принять", callback_data=f"{CB_RP_ACCEPT}:{int(offer_id)}", style="success"),
        _ikb("Отклонить", callback_data=f"{CB_RP_DECLINE}:{int(offer_id)}", style="danger")
    )
    return kb

def _parse_inline_infect_query(query: str):
    raw = (query or "").strip()
    if not raw:
        return None

    pref_tid, _pref_tok, pref_tail = _inline_strip_target_prefix(raw)
    if pref_tid is not None:
        if not pref_tail:
            return {"kind": "U", "target": int(pref_tid), "count": 1}
        if pref_tail.isdigit():
            return {"kind": "U", "target": int(pref_tid), "count": max(1, int(pref_tail))}
        return None

    toks = raw.split()
    if not toks:
        return None

    if len(toks) >= 2 and toks[0].isdigit():
        tid = _resolve_or_create_infect_target(toks[1])
        if tid is not None:
            return {"kind": "U", "target": int(tid), "count": max(1, int(toks[0]))}

    tid0 = _resolve_or_create_infect_target(toks[0])
    if tid0 is not None:
        cnt = int(toks[1]) if len(toks) >= 2 and toks[1].isdigit() else 1
        return {"kind": "U", "target": int(tid0), "count": max(1, cnt)}

    idx = 0
    cnt = 1
    if toks[0].isdigit():
        cnt = max(1, int(toks[0]))
        idx = 1

    if idx >= len(toks):
        return None

    key = toks[idx].lower()
    mode = INF_MODE_SYNONYMS.get(key)
    if mode and mode != "c":
        if idx + 1 < len(toks) and toks[idx + 1].isdigit():
            cnt = max(1, int(toks[idx + 1]))
        return {"kind": "M", "mode": mode, "count": cnt, "filter": "n"}

    return None

def _inline_infect_preview_text(req: dict) -> str:
    if (req.get("kind") or "") == "U":
        tid = int(req["target"])
        cnt = max(1, int(req["count"] or 1))
        word = _ru_form(cnt, "патоген", "патогена", "патогенов")
        return (
            f"🦠 Подготовлено заражение цели {public_user_tag(tid)}\n"
            f"🧪 Будет использовано: {cnt} {word}\n\n"
            "Нажмите кнопку ниже, чтобы выполнить заражение."
        )

    mode = str(req.get("mode") or "r")
    cnt = max(1, int(req.get("count") or 1))
    word = _ru_form(cnt, "патоген", "патогена", "патогенов")
    mode_txt = {
        "r": "случайного объекта",
        "p": "объекта с большим био-опытом",
        "m": "объекта с меньшим био-опытом",
        "e": "объекта с равным био-опытом",
    }.get(mode, "объекта")

    return (
        f"🦠 Подготовлено заражение {mode_txt}\n"
        f"🧪 Будет использовано: {cnt} {word}\n\n"
        "Нажмите кнопку ниже, чтобы выполнить заражение."
    )

def _inline_article(article_id: str, title: str, desc: str, text: str, reply_markup=None, thumb_url: str = None) -> InlineQueryResultArticle:
    text = premiumize_html_text(text or "")
    try:
        content = InputTextMessageContent(text, parse_mode="HTML", disable_web_page_preview=True)
    except TypeError:
        content = InputTextMessageContent(text, parse_mode="HTML")

    turl = (thumb_url or INLINE_THUMB_DEFAULT_URL)

    try:
        return InlineQueryResultArticle(
            id=article_id,
            title=title,
            description=desc,
            input_message_content=content,
            reply_markup=reply_markup,
            thumbnail_url=turl,
        )
    except TypeError:
        pass

    try:
        return InlineQueryResultArticle(
            id=article_id,
            title=title,
            description=desc,
            input_message_content=content,
            reply_markup=reply_markup,
            thumb_url=turl,
        )
    except TypeError:
        pass

    try:
        return InlineQueryResultArticle(
            id=article_id,
            title=title,
            description=desc,
            input_message_content=content,
            reply_markup=reply_markup,
        )
    except TypeError:
        pass

    return InlineQueryResultArticle(
        id=article_id,
        title=title,
        description=desc,
        input_message_content=content,
    )

def _safe_answer_inline_query(inline_query_id: str, results, *, cache_time: int = 0, is_personal: bool = True) -> bool:
    try:
        bot.answer_inline_query(
            inline_query_id,
            results,
            cache_time=cache_time,
            is_personal=is_personal
        )
        return True
    except Exception as e:
        msg = str(e).lower()

        if (
            "query is too old" in msg
            or "response timeout expired" in msg
            or "query id is invalid" in msg
        ):
            return False

        if (
            "remote end closed connection without response" in msg
            or "connection aborted" in msg
            or "remotedisconnected" in msg
            or "protocolerror" in msg
            or "read timed out" in msg
            or "connect timeout" in msg
            or "connectionerror" in msg
        ):
            return False

        raise

@bot.inline_handler(func=lambda q: True)
def inline_query_handler(inline_query):
    try:
        uid = int(inline_query.from_user.id)

        if is_bot_banned(uid):
            bot.answer_inline_query(inline_query.id, [], cache_time=0, is_personal=True)
            return

        upsert_user(inline_query.from_user)
        _merge_placeholder_to_real_user(inline_query.from_user)
        ensure_creator_is_support()
        ensure_lab_exists(uid)

        q_raw = (inline_query.query or "").strip()
        q = q_raw.lower()

        results = []
        iq_chat_type = str(getattr(inline_query, "chat_type", "") or "").lower()


        my_cid, _ = get_user_corp_resolved(uid)
        my_corp = corp_by_id(my_cid) if my_cid > 0 else None

        inline_target_id, inline_target_token, inline_tail_raw = _inline_strip_target_prefix(q_raw)
        inline_tail = inline_tail_raw.lower().strip()

        # @username + выбор баланса/досье/корпы
        if inline_target_token:
            if inline_target_id is not None:
                if _inline_wants_lab(inline_tail):
                    text, rm = _render_inline_lab_for_viewer(uid, int(inline_target_id))
                    results.append(_inline_article(
                        article_id=f"lab_{uid}_{int(inline_target_id)}",
                        title="Досье лаборатории",
                        desc=f"Отправить в чат досье лаборатории {_inline_plain_target_name(int(inline_target_id))}",
                        text=text,
                        reply_markup=rm if int(inline_target_id) == int(uid) else None,
                        thumb_url=INLINE_THUMB_LAB_URL
                    ))

                if _inline_wants_balance(inline_tail):
                    text, rm = _render_inline_balance_for_viewer(uid, int(inline_target_id))
                    results.append(_inline_article(
                        article_id=f"bal_{uid}_{int(inline_target_id)}",
                        title="Баланс",
                        desc=f"Отправить в чат информацию баланса {_inline_plain_target_name(int(inline_target_id))}",
                        text=text,
                        reply_markup=rm if int(inline_target_id) == int(uid) else None,
                        thumb_url=INLINE_THUMB_BAL_URL
                    ))

                if _inline_wants_corp(inline_tail):
                    text, rm = _render_inline_corp_for_viewer(uid, int(inline_target_id))
                    results.append(_inline_article(
                        article_id=f"corp_{uid}_{int(inline_target_id)}",
                        title="Досье корпорации",
                        desc=f"Отправить в чат досье корпорации {_inline_plain_target_name(int(inline_target_id))}",
                        text=text,
                        reply_markup=rm,
                        thumb_url=INLINE_THUMB_CORP_URL
                    ))

        else:
            # своё досье лаборатории
            if (not q) or (q in ("моя лаба", "моя лаборатория", "лаб", "лаборатория")) or q.startswith(("лаб", "лабо", "моя л")):
                text = render_lab(uid)
                results.append(_inline_article(
                    article_id=f"lab_{uid}",
                    title="Досье лаборатории",
                    desc="Отправить в чат досье вашей лаборатории",
                    text=text,
                    reply_markup=kb_lab_dossier_inline(uid),
                    thumb_url=INLINE_THUMB_LAB_URL
                ))
                
            # свой баланс
            if (not q) or (q in ("баланс", "мешок", "кошелек", "кошелёк")) or q.startswith(("бал", "меш", "кош")):
                text = render_balance(uid)
                results.append(_inline_article(
                    article_id=f"bal_{uid}",
                    title="Баланс",
                    desc="Отправить в чат информацию вашего баланса",
                    text=text,
                    reply_markup=kb_balance_self(uid),
                    thumb_url=INLINE_THUMB_BAL_URL
                ))

            # своё досье корпорации
            if my_corp and (
                (not q)
                or (q in ("корп", "корпорация", "моя корп", "моя корпорация", "досье корпорации"))
                or q.startswith(("корп", "моя к", "досье корп"))
            ):
                text, rm = render_corp_info_text(my_corp, uid)
                results.append(_inline_article(
                    article_id=f"corp_{uid}_{my_cid}",
                    title="Досье корпорации",
                    desc="Отправить в чать досье вашей корпорации",
                    text=text,
                    reply_markup=rm,
                    thumb_url=INLINE_THUMB_CORP_URL
                ))

        # inline-заражение
        inf_req = _parse_inline_infect_query(q_raw)
        if inf_req:
            if (inf_req.get("kind") or "") == "U":
                tid = int(inf_req["target"])
                cnt = max(1, int(inf_req["count"] or 1))
                results.append(_inline_article(
                    article_id=f"infect_u_{uid}_{tid}_{cnt}",
                    title="Заразить",
                    desc=_inline_infect_desc(inf_req),
                    text=_inline_infect_preview_text(inf_req),
                    reply_markup=kb_inline_infect_execute_user(uid, tid, cnt),
                    thumb_url=INLINE_THUMB_INFECT_URL
                ))
            else:
                mode = str(inf_req["mode"] or "r")
                cnt = max(1, int(inf_req["count"] or 1))
                results.append(_inline_article(
                    article_id=f"infect_m_{uid}_{mode}_{cnt}",
                    title="Заразить",
                    desc=_inline_infect_desc(inf_req),
                    text=_inline_infect_preview_text(inf_req),
                    reply_markup=kb_inline_infect_execute_mass(uid, mode, cnt),
                    thumb_url=INLINE_THUMB_INFECT_URL
                ))

        # inline RP — только из приватного чата
        if iq_chat_type == "private":
            rp_action, rp_extra_tail, rp_comment_text = _parse_inline_rp_query(q_raw, uid)
            if rp_action:
                action_ref = _encode_rp_action_ref(rp_action)
                offer_id = _create_rp_offer(uid, action_ref, extra_tail=rp_extra_tail, comment_text=rp_comment_text)
                actor_tag = public_user_tag(uid)
                offer_text = f"Пользователь {actor_tag} предлагает вам действие..."

                results.append(_inline_article(
                    article_id=f"rp_{uid}_{abs(hash(action_ref))}_{offer_id}",
                    title=f"{rp_action['emoji']}{rp_action['trigger']}",
                    desc=f"Предложить собеседнику {rp_action['trigger']}",
                    text=offer_text,
                    reply_markup=kb_inline_rp_offer(int(offer_id)),
                    thumb_url=INLINE_THUMB_RP_URL
                ))

        # калькулятор
        if not inline_target_token:
            calc_req = _inline_calc_req_from_query(q_raw)
            if calc_req:
                calc_title = calc_req["title"]
                calc_desc = calc_req["desc"]
                calc_text = calc_req["text"]
                calc_rm = calc_req.get("reply_markup")
                ready_suffix = "ready" if calc_req.get("ready") else "hint"

                results.append(_inline_article(
                    article_id=f"calc_{uid}_{ready_suffix}_{abs(hash(q_raw))}",
                    title=calc_title,
                    desc=calc_desc,
                    text=calc_text,
                    reply_markup=calc_rm,
                    thumb_url=INLINE_THUMB_CALC_URL
                ))

        if results:
            _safe_answer_inline_query(inline_query.id, results[:8], cache_time=0, is_personal=True)
            return

        _safe_answer_inline_query(inline_query.id, [], cache_time=1, is_personal=True)
    except Exception as e:
        send_error_report("inline_query_handler", e)
        try:
            _safe_answer_inline_query(inline_query.id, [], cache_time=2, is_personal=True)
        except Exception:
            pass

@bot.message_handler(
    content_types=["photo", "video"],
    func=lambda m: (m.chat.type == "private" and report_get_state(int(m.from_user.id))[0] == "await_content")
)
def on_report_media(message):
    try:
        uid = int(message.from_user.id)
        if is_bot_banned(uid):
            stage, cat = report_get_state(int(uid))
            if not (stage == "await_content" and str(cat or "").upper() == "APPEAL"):
                bot.reply_to(message, render_bot_ban_text(uid), disable_web_page_preview=True)
                return

        upsert_user(message.from_user)
        _handle_report_content_message(message)
    except Exception as e:
        send_error_report("on_report_media", e)

@bot.message_handler(
    content_types=["document"],
    func=lambda m: bool(parse_message_as_command((getattr(m, "caption", "") or "")))
)
def on_document_db_command(message):
    try:
        parsed = parse_message_as_command((getattr(message, "caption", "") or ""))
        if not parsed:
            return ContinueHandling

        if parsed.cmd != "db_fife_upd":
            return ContinueHandling

        if getattr(message, "from_user", None) is None:
            return ContinueHandling

        uid = int(message.from_user.id)
        upsert_user(message.from_user)
        _merge_placeholder_to_real_user(message.from_user)

        if message.chat.type == "private":
            set_pm_opened(int(uid), 1)
            set_notify_prefs(int(uid), 0, 0)

        handle_owner_db_commands(message, parsed)
    except Exception as e:
        send_error_report("on_document_db_command", e)

    return ContinueHandling

@bot.message_handler(
    content_types=[
        "text", "photo", "video", "document", "audio", "voice", "sticker",
        "animation", "video_note", "location", "contact", "poll", "dice"
    ],
    func=lambda m: True
)
def observe_seen_users(message):
    try:
        if (getattr(message.chat, "type", "") or "").lower() in ("group", "supergroup"):
            if not is_channel_sender_message(message):
                remember_bot_group_chat(
                    int(message.chat.id),
                    title=(getattr(message.chat, "title", "") or ""),
                    chat_type=(getattr(message.chat, "type", "") or "group"),
                    is_active=1
                )
                u = getattr(message, "from_user", None)
                if u:
                    remember_chat_member(int(message.chat.id), u)

                rm = getattr(message, "reply_to_message", None)
                if rm and getattr(rm, "from_user", None):
                    ru = rm.from_user
                    remember_chat_member(int(message.chat.id), ru)

                for nu in (getattr(message, "new_chat_members", None) or []):
                    if nu:
                        remember_chat_member(int(message.chat.id), nu)
    except Exception:
        pass

    return ContinueHandling()

# MAIN ROUTER
@bot.message_handler(content_types=["text"])
def text_router(message):
    set_chat_name_context(int(getattr(getattr(message, "chat", None), "id", 0) or 0))
    try:
        if (getattr(message.chat, "type", "") or "").lower() == "channel":
            return
        if is_channel_sender_message(message):
            return

        if getattr(message, "from_user", None) is None:
            return

        uid = int(message.from_user.id)

        if is_bot_banned(uid):
            if message.chat.type != "private":
                return
        
            stage, cat = report_get_state(int(uid))
            parsed_banned = parse_message_as_command(message.text or "")
        
            if stage == "await_content" and str(cat or "").upper() == "APPEAL":
                upsert_user(message.from_user)
                _merge_placeholder_to_real_user(message.from_user)
                set_pm_opened(int(uid), 1)
                set_notify_prefs(int(uid), 0, 0)
                ensure_creator_is_support()
        
                if parsed_banned:
                    if parsed_banned.cmd == "report":
                        handle_report_command(message)
                        return
        
                    report_clear_state(int(uid))
                else:
                    if _handle_report_content_message(message):
                        return
        
            if parsed_banned and parsed_banned.cmd == "report":
                upsert_user(message.from_user)
                _merge_placeholder_to_real_user(message.from_user)
                set_pm_opened(int(uid), 1)
                set_notify_prefs(int(uid), 0, 0)
                ensure_creator_is_support()
                handle_report_command(message)
                return
        
            bot.reply_to(message, render_bot_ban_text(uid), disable_web_page_preview=True)
            return

        upsert_user(message.from_user)
        _merge_placeholder_to_real_user(message.from_user)
        if message.chat.type == "private":
            set_pm_opened(int(uid), 1)
            set_notify_prefs(int(uid), 0, 0)
        if getattr(message, "via_bot", None) is not None:
            return
        if message.chat.type in ("group", "supergroup"):
            remember_chat_member(message.chat.id, message.from_user)       
        ensure_creator_is_support()

        parsed = parse_message_as_command(message.text or "")
        stage, cat = report_get_state(int(uid))

        if message.chat.type == "private" and stage == "await_content":
            if parsed:
                if parsed.cmd == "report":
                    handle_report_command(message)
                    return

                report_clear_state(int(uid))
            else:
                if _handle_report_content_message(message):
                    return

        if not parsed:
            if try_handle_rp_action_message(message):
                return
            return

        sign0 = leading_sign_after_bot_prefix(message.text or "")
        if sign0 and parsed.cmd not in SIGNED_COMMANDS_ALLOWED:
            return

        if parsed.cmd in STRICT_NO_EXTRA_ARGS_CMDS and (parsed.args or "").strip():
            return
        
        if parsed.cmd in ("timer_delete",):
            if not strict_single_numeric_arg_ok(parsed):
                return

        if parsed.cmd in ("promo_delete", "promo_use", "bot_ban", "bot_unban", "remake_lab", "edit_k", "edit_b"):
            if not strict_single_word_arg_ok(parsed):
                return

        if parsed.cmd in (
            "top_users", "top_users_chat",
            "top_diseases", "top_diseases_chat",
            "top_corps", "top_corps_chat",
        ) and not has_explicit_bot_prefix(message.text or ""):
            return
        if parsed.cmd in ("balance", "lab", "mylab"):
            bad = not strict_single_target_args_ok(message, parsed, allow_empty=True)
            if bad:
                if (parsed.args or "").strip() and try_handle_rp_action_message(message):
                    return
                return

        if parsed.cmd in ("corp_invite",):
            bad = not strict_single_target_args_ok(message, parsed, allow_empty=False)
            if bad:
                if (parsed.args or "").strip() and try_handle_rp_action_message(message):
                    return
                return

        if parsed.cmd == "my_owner":
            handle_my_owner_command(message, parsed)
            return

        if parsed.cmd == "my_owner_remove":
            handle_my_owner_remove_command(message, parsed)
            return

        if parsed.cmd == "owner":
            handle_owner_command(message, parsed)
            return

        if parsed.cmd == "owner_remove":
            handle_owner_remove_command(message, parsed)
            return

        if parsed.cmd == "agent":
            handle_agent_command(message, parsed)
            return

        if parsed.cmd == "agent_remove":
            handle_agent_remove_command(message, parsed)
            return
        
        # data base
        if parsed.cmd in ("db_fife", "db_fife_stat", "db_fife_msg", "db_fife_upd", "its"):
            handle_owner_db_commands(message, parsed)
            return

        if parsed.cmd == "delete_user_db":
            handle_delete_user_db_command(message, parsed)
            return

        # коффициенты заражения
        if parsed.cmd == "edit_k":
            handle_edit_k_command(message, parsed)
            return

        if parsed.cmd == "edit_b":
            handle_edit_b_command(message, parsed)
            return

        if parsed.cmd == "cof_inf_stats":
            handle_cof_inf_stats_command(message, parsed)
            return

        # коэффициенты дуэли
        if parsed.cmd == "duel_cof_stats":
            handle_duel_cof_stats_command(message, parsed)
            return

        if parsed.cmd == "duel_cof_break":
            handle_duel_cof_break_command(message, parsed)
            return

        if parsed.cmd == "duel_cof_break_bon":
            handle_duel_cof_break_bon_command(message, parsed)
            return

        if parsed.cmd == "duel_cof_aim":
            handle_duel_cof_aim_command(message, parsed)
            return

        if parsed.cmd == "duel_cof_base_pts":
            handle_duel_cof_base_pts_command(message, parsed)
            return

        if parsed.cmd == "duel_rounds":
            handle_duel_rounds_command(message, parsed)
            return

        # /agents
        if parsed.cmd == "agents_panel":
            handle_agents_panel_command(message)
            return

        # помощь
        if parsed.cmd == "help":
            handle_help_command(message)
            return

        # пинг
        if parsed.cmd == "ping":
            handle_ping_command(message)
            return

        # рп стата
        if parsed.cmd == "rp_stats":
            handle_rp_stats_command(message)
            return
        
        # мрп
        if parsed.cmd == "mrp_add":
            handle_mrp_add_command(message)
            return

        if parsed.cmd == "mrp_delete":
            handle_mrp_delete_command(message, parsed)
            return

        if parsed.cmd == "mrp_list":
            handle_mrp_list_command(message)
            return

        # admin service
        if parsed.cmd in ("bot_ban", "bot_unban", "remake_lab"):
            handle_admin_service_commands(message, parsed)
            return

        if parsed.cmd in ("name_lock_user", "name_lock_lab", "name_lock_pat", "name_lock_corp"):
            handle_admin_name_restriction_command(message, parsed)
            return

        if parsed.cmd == "blacklist":
            handle_blacklist_command(message)
            return
        
        if parsed.cmd == "users_list":
            handle_users_list_command(message)
            return

        # промокоды
        if parsed.cmd == "promo_generate":
            handle_promo_generate_command(message)
            return

        if parsed.cmd == "promo_create":
            handle_promo_create_command(message)
            return

        if parsed.cmd == "promo_all":
            handle_promo_all_command(message)
            return

        if parsed.cmd == "promo_delete":
            handle_promo_delete_command(message, parsed)
            return

        if parsed.cmd == "promo_use":
            handle_promo_use_command(message, parsed)
            return

        # список команд
        if parsed.cmd == "commands_link":
            handle_commands_link(message)
            return
        
        # айди помошник
        if parsed.cmd == "emoji_pack_ids":
            handle_emoji_pack_ids_command(message, parsed)
            return

        # /settings
        if parsed.cmd == "settings":
            handle_settings_command(message)
            return
        
        # /report
        if parsed.cmd == "report":
            handle_report_command(message)
            return

        # timers
        if parsed.cmd in (
            "timer_add_rel", "timer_add_abs", "timer_add_cycle",
            "timer_delete", "timer_clear_all", "timer_list"
        ):
            handle_timer_commands(message, parsed)
            return

        # автоудаление
        if parsed.cmd in ("chat_autodel_set", "chat_autodel_status", "chat_autodel_off"):
            handle_chat_autodelete_commands(message, parsed)
            return

        # приватные настройки
        if parsed.cmd in ("balance_hide", "balance_show", "lab_hide", "lab_show"):
            handle_privacy_toggle(message, parsed.cmd)
            return

        # пользовательские настройки
        if parsed.cmd in ("corp_notify_on", "corp_notify_off", "gender_set", "rp_on", "rp_off"):
            handle_user_pref_command(message, parsed)
            return
        
        # уведомление
        if parsed.cmd in ("notify_on", "notify_off"):
            handle_notify_toggle(message, parsed.cmd)
            return

        # автоответчик
        if parsed.cmd in ("autoanswer_status", "autoanswer_on", "autoanswer_off"):
            handle_autoanswer_toggle(message, parsed.cmd)
            return

        # дуэли
        if parsed.cmd in (
            "duel_call", "duel_call_stake", "duel_accept", "duel_decline", "duel_cancel",
            "duel_fire", "duel_aim", "duel_break_aim", "duel_surrender",
            "duel_bets_list", "duel_bet", "duel_stats"
        ):
            if parsed.cmd == "duel_call":
                args = (parsed.args or "").strip()
                if args and not strict_single_target_args_ok(message, parsed, allow_empty=False):
                    return

            elif parsed.cmd == "duel_call_stake":
                target_id_chk, _target_user_chk, stake_chk, _err_chk = _duel_parse_call_args(
                    message,
                    parsed,
                    with_stake=True
                )
                if target_id_chk is None or int(stake_chk or 0) <= 0:
                    return

            handle_duel_commands(message, parsed)
            return

        # заразить
        if parsed.cmd == "infect":
            handle_infect_command(message, parsed)
            return

        # диверсия
        if parsed.cmd == "sabotage":
            handle_sabotage_command(message, parsed)
            return

        # баланс
        if parsed.cmd == "balance":
            handle_balance_command(message, parsed)
            return

        # синтез
        if parsed.cmd == "synth":
            handle_synth_command(message)
            return
        
        # улучшения навыков
        if parsed.cmd in ("upgrade_preview", "upgrade_buy"):
            handle_upgrade_command(message, parsed)
            return

        # калькулятор
        if parsed.cmd in ("calc", "calc_upg", 
                          "calc_chance", "calc_buff", 
                          "calc_exp", "calc_duel"):
            if not has_explicit_bot_prefix(getattr(message, "text", "") or ""):
                return
            handle_calc_command(message, parsed)
            return

        # использовать вакцину
        if parsed.cmd == "use_vaccine":
            uid = int(message.from_user.id)
            doses, target_id, target_user_obj = _parse_use_vaccine_args(message, parsed)
        
            if target_user_obj is not None:
                capture_user_context(message, target_user_obj)
        
            if target_id is None:
                target_id = int(uid)
        
            if int(target_id) == int(uid):
                fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
                now = now_ts()
        
                if fever_until <= now:
                    bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости использовать вакцину.")
                    return
        
                status, used = try_use_vaccine(uid, int(doses))
        
                if status == "OK":
                    word = _ru_form(int(used), "единица", "единицы", "единиц")
                    bot.reply_to(message, f"💉 Вакцина излечила вас от горячки.\n🧾 Потрачено {int(used)} {word} вакцины")
                elif status == "FAIL":
                    bot.reply_to(message, VACCINE_FAIL_TEXT, disable_web_page_preview=True, reply_markup=kb_vaccine_retry(uid))
                elif status == "NO_VACCINE":
                    price_txt = _fmt_bio_res(get_vaccine_price(uid))
                    kb = InlineKeyboardMarkup()
                    kb.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=_cb_buy_vaccine(uid), style="primary"))
                    bot.reply_to(
                        message,
                        f"💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: {price_txt}, команда \"<code>Био купить вакцину</code>\"",
                        parse_mode="HTML",
                        disable_web_page_preview=True,
                        reply_markup=kb
                    )
                else:
                    bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости использовать вакцину.")
                return
        
            if not same_corp(int(uid), int(target_id)):
                bot.reply_to(message, "📑 Использовать вакцины на другого игрока можно только внутри вашей Корпорации.")
                return
        
            fever_until, fever_pat, _ = get_fever_and_vaccines(int(target_id))
            now = now_ts()
        
            if fever_until <= now:
                bot.reply_to(message, "📝 У цели нет горячки. Нет необходимости использовать вакцину.")
                return
        
            status, used = try_use_vaccine_for_target(int(uid), int(target_id), int(doses))
            target_tag = _corp_actor_tag(int(target_id))
        
            if status == "OK":
                word = _ru_form(int(used), "единица", "единицы", "единиц")
                bot.reply_to(
                    message,
                    f"💉 Горячка игрока <b>{target_tag}</b> устранена.\n🧾 Потрачено {int(used)} {word} вакцины",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            elif status == "FAIL":
                bot.reply_to(
                    message,
                    f"🧿 Вакцина не смогла справиться с болезнью игрока <b>{target_tag}</b>.",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            elif status == "NO_VACCINE":
                bot.reply_to(message, "💉 Сейчас у вас нет ни одной вакцины.")
            elif status == "NOT_SAME_CORP":
                bot.reply_to(message, "📑 Использовать вакцины на другого игрока можно только внутри вашей Корпорации.")
            else:
                bot.reply_to(message, "📝 У цели нет горячки. Нет необходимости использовать вакцину.")
            return

        # купить вакцину
        if parsed.cmd == "buy_vaccine":
            uid = int(message.from_user.id)
            fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
            now = now_ts()

            if fever_until <= now:
                bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости покупать вакцину.")
                return

            if vac_cnt > 0:
                kb = InlineKeyboardMarkup()
                kb.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=_cb_use_vaccine(uid), style="primary"))
                bot.reply_to(
                    message,
                    "💉 У вас нет необходимости покупать вакцину.  Для быстрого выздоровления используйте вакцину\n"
                    "команда \"<code>Био использовать вакцину</code>\"",
                    disable_web_page_preview=True,
                    reply_markup=kb
                )
                return

            status, spent_res, spent_mat = try_buy_vaccine(uid)
            if status == "NO_MONEY":
                set_balance_chain_state_from_message(
                    message,
                    BALCHAIN_VACCINE,
                    "Повторить покупку",
                    {"action": "buy"}
                )
                bot.reply_to(message, "📝 У вас недостаточно средств.", reply_markup=kb_open_balance(int(uid)))
            elif status == "NO_FEVER":
                bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости покупать вакцину.")
            elif status == "FAIL":
                bot.reply_to(message, VACCINE_FAIL_TEXT, disable_web_page_preview=True, reply_markup=kb_vaccine_retry(uid))
                st = get_balance_chain_state(int(uid))
                if st and str(st.get("chain_kind") or "") == BALCHAIN_VACCINE:
                    clear_balance_chain_state(int(uid))

            else:
                bot.reply_to(
                    message,
                    "💉 Вакцина излечила вас от горячки.\n"
                    f"🧾 Потрачено {vaccine_spent_text(spent_res, spent_mat)}",
                    disable_web_page_preview=True
                )
            return

        # топы
        if parsed.cmd in (
            "top_users", "top_diseases", "top_users_chat",
            "top_diseases_chat", "top_corps", "top_corps_chat"
        ):
            handle_top_commands(message, parsed)
            return

        # корпорации
        if parsed.cmd in (
            "corp_create", "corp_delete", "corp_open", "corp_close", "corp_rename",
            "corp_reg", "corp_info", "corp_my", "corp_join", "corp_invite",
            "corp_req_accept", "corp_req_reject", "corp_req_list",
            "corp_deputy", "corp_deputy_remove", "corp_kick", "corp_leave", "corp_transfer_owner",
            "corp_send_res", "corp_send_mat"
        ):
            handle_corp_commands(message, parsed)
            return
        
        # лаборатория
        if parsed.cmd in (
            "lab", "mylab", "labname", "pathogenname",
            "labname_clear", "pathogenname_clear",
            "chatname_set", "chatname_show", "chatname_clear",
            "lab_delete", "lab_delete_now", "restore_lab", "lab_delete_confirm_phrase",
            "pathogens_info", "pathogen_info"
        ):
            handle_lab_commands(message, parsed)
            return

    except Exception as e:
        send_error_report("text_router", e)
    finally:
        clear_chat_name_context()

if __name__ == "__main__":
    init_db()
    init_deleted_db()

    try:
        migrated = migrate_old_main_db_if_needed()
        if migrated:
            print("[DB] old_data -> data migration completed")
    except Exception as e:
        send_error_report("migrate_old_main_db_if_needed", e)
        raise

    ensure_creator_is_support()

    try:
        _maybe_promote_unavailable_creator(force=True)
    except Exception as e:
        send_error_report("_maybe_promote_unavailable_creator_startup", e)

    refresh_bot_identity()
    threading.Thread(target=_infection_daemon, daemon=True).start()
    threading.Thread(target=_pathogen_factory_daemon, daemon=True).start()
    threading.Thread(target=_vaccine_factory_daemon, daemon=True).start()
    threading.Thread(target=_housekeeping_daemon, daemon=True).start()
    print(f"@{BOT_USERNAME or 'unknown'} started...")
    while True:
        try:
            if not BOT_USERNAME:
                refresh_bot_identity()            
            bot.infinity_polling(
                skip_pending=True,
                timeout=10,
                long_polling_timeout=20,
                allowed_updates=["message", "inline_query", "callback_query", "chat_member", "my_chat_member"]
            )
        except Exception as e:
            send_error_report("infinity_polling", e)
            time.sleep(5)