import os
import re
import io
import sys
import json
import time
import heapq
import random
import sqlite3
import itertools
import threading
import traceback
import unicodedata
from dataclasses import dataclass
from typing import Optional, Tuple, List, Dict

import telebot
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
URL_COMMANDS = "http://www.example.com/"
URL_SUPPORT_CHAT = "https://t.me/dnd_bot_tgk?direct"
URL_DEV_CHANNEL = "https://t.me/dnd_bot_tgk"
# миниатюры
INLINE_THUMB_LAB_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/lab.png"
INLINE_THUMB_BAL_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/balance.png"
INLINE_THUMB_CALC_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/calculate.png"  
INLINE_THUMB_CORP_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/corp.png"
INLINE_THUMB_INFECT_URL = "https://raw.githubusercontent.com/andreavitaev/biobot/image/infect.png"
# запасной вариант
INLINE_THUMB_DEFAULT_URL = "https://raw.githubusercontent.com/andreavitaev/boss-rush-assets/main/thumb_1.jpg"

ONLINE_TTL_SECONDS = 300  # 5 минут онлайн по последней активности с ботом

# PATHS / DB
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
DB_PATH = os.path.join(DATA_DIR, "bio_war.db")
DELETED_DB_PATH = os.path.join(DATA_DIR, "deleted_labs.db")
os.makedirs(DATA_DIR, exist_ok=True)

# Random infection events
RANDOM_EVENTS_PATH = os.path.join(DATA_DIR, "random_events.txt")
_RANDOM_EVENTS_CACHE: Optional[list[str]] = None

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

def random_event_pct(qualification_level: int) -> float:
    try:
        q = int(qualification_level or 0)
    except Exception:
        q = 0
    pct = 20.0 - (q // 10) * 0.1
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
        kb.add(InlineKeyboardButton("Выключить", callback_data=f"{CB_AO_TOGGLE}:{uid}:0"))
    else:
        kb.add(InlineKeyboardButton("Включить", callback_data=f"{CB_AO_TOGGLE}:{uid}:1"))
    return kb

def kb_autoanswer_open(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Статус автоответчика", callback_data=f"{CB_AO_MENU}:{uid}"))
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
        f"✅Доступно авто-ответов: {avail}\n"
        f"⏱️Сбросится через {_format_hm_from_seconds(left)}"
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
        left = fever_until - now
        txt = (
            "🌡️ [Автоответчик]:\n"
            f"❎ Не удалось заразить {org_q}: Горячка, вызванная {_pat_for_fever(fever_pat)}, "
            f"время выздоровления {_format_hms(left)}"
        )
        _auto_send_reply(chat_id, reply_to_msg_id, txt)
        db_exec("UPDATE autoanswer_state SET waiting_hot=1, waiting_hot_since=? WHERE user_id=?",
                (int(now), defender_id), commit=True)
        return

    ready = int(lab_def["ready_pathogens"] or 0)
    if ready <= 0:
        txt = (
            "🧪 [Автоответчик]:\n"
            f"❎ Не удалось заразить {org_q}: не осталось патогенов"
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
            "💢 [Автоответчик]:\n"
            f"❎ Не удалось заразить {org_q}: {h(ev)}"
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
    roll = random.randint(1, 100)
    if roll > p_success:
        txt = (
            "🛡 [Автоответчик]:\n"
            f"❎ Не удалось заразить {org_q}: иммунитет справился с заражением"
        )
        _auto_send_reply(chat_id, reply_to_msg_id, txt)
        return

    texp = int(trow["be"] if trow else 0)
    gained = max(1, texp // 2)

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
                "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name) "
                "VALUES (?,?,?,?,?,?,1,?) "
                "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                "start_ts=excluded.start_ts, end_ts=excluded.end_ts, add_bio_res=excluded.add_bio_res, "
                "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name",
                (defender_id, organizer_id, now, end_ts, gained, next_payout, pathogen_name)
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
        "🦠 [Автоответчик]:\n"
        f"✅ Успешное заражение {org_q}\n"
        f"☣️‍ +{_fmt_k(int(gained))} {exp_word}"
    )
    _auto_send_reply(chat_id, reply_to_msg_id, txt)

DB_LOCK = threading.RLock()

# BOT threaded
bot = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML", threaded=True, num_threads=8)

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

# Имя/username бота
try:
    _me = bot.get_me()
    BOT_USERNAME = _me.username or ""
    BOT_TITLE = (_me.first_name or "").strip() or "Bio War bot"
except Exception:
    BOT_USERNAME = ""
    BOT_TITLE = "Bio War bot"

# Коды ошибок файлы.txt (анти-спам файлами)
_ERROR_REPORT_LAST: Dict[str, int] = {}
ERROR_REPORT_COOLDOWN_SEC = 60

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

        bio = io.BytesIO(payload)
        bio.name = f"bot_error_{now}.txt"
        bot.send_document(OWNER_ID, bio, caption=f"Ошибка бота: {context}")
    except Exception:
        pass

def _thread_excepthook(args):
    try:
        text = "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback))
        bio = io.BytesIO(text.encode("utf-8", errors="replace"))
        bio.name = f"thread_error_{int(time.time())}.txt"
        bot.send_document(OWNER_ID, bio, caption=f"Поток: {getattr(args.thread, 'name', 'thread')}")
    except Exception:
        pass
    
threading.excepthook = _thread_excepthook

def _sys_excepthook(exc_type, exc_value, exc_tb):
    try:
        text = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        bio = io.BytesIO(text.encode("utf-8", errors="replace"))
        bio.name = f"fatal_error_{int(time.time())}.txt"
        bot.send_document(OWNER_ID, bio, caption="Необработанная ошибка")
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
    "🦠": "5451936901772616837",
    "☠️": "",
    "🧿": "5296426834748002089",
    "🛡️": "5210988351703771812",
    "⚗️": "5262680005393025261",
    "💉": "5472317878801800869",
    "🧪": "5411512278740640309",
    "📟": "5197423165650795840",
    "🛰️": "5195361551283942795",
    "🧮": "5190741648237161191",
    "⏱️": "5258258882022612173",
    "⛑️": "5264892613630111886",
    "🏷️": "5255806717689631058",
    "✉️": "",
    "📑": "",
    "📋": "",
    "📝": "5334882760735598374",
    "✅": "5260416304224936047",
    "❌": "5260342697075416641",
    "⚠️": "5447381715293074599",
    "🔒": "5258458340303866282",
    "🔓": "5256212970056224341",
    "🔊": "5260325873688518261",
    "🔇": "5258267368877989660",
    "⏳": "5199457120428249992",
    "🤧": "5370880659759831851",
    "🤒": "5373262021556967911",
    "🕵️‍♂️": "",
    "👨‍🔬": "",
    "👮": "",
    "🥷": "5195316351048121745",
    "👨‍⚕️": "5429363657471434941",
    "🧑‍✈️": "",
    "🧑‍💼": "",
    "🏥": "5264827875588077689",
    "🏣": "5264716824913671598",
    "🏢": "5264733042710181045",
    "💎": "5343636681473935403",
    "🪬": "5276489300207217985",
    "💬": "5255727011686553638",
    "👋": "5208853155957209306",
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

def display_name(first_name: str, last_name: str, username: str, user_id: int) -> str:
    full = _strip_invisible(((first_name or "").strip() + " " + (last_name or "").strip())).strip()
    if full and (not _is_bad_single_char_name(full)) and (not _is_decorative_only_name(full)):
        return full

    un = _strip_invisible(username or "")  # username без "@"
    if un:
        return un

    return str(int(user_id))

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
        href = f"tg://user?id={uid}"

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
        return premiumize_html_text(value)
    return value

def _premiumize_caption_kwargs(kwargs: dict) -> dict:
    if "caption" in kwargs and isinstance(kwargs.get("caption"), str):
        kwargs["caption"] = premiumize_html_text(kwargs["caption"])
    return kwargs

def _bot_send_message_premium(chat_id, text, *args, **kwargs):
    return _REAL_BOT_SEND_MESSAGE(chat_id, _premium_text_payload(text), *args, **kwargs)

def _bot_reply_to_premium(message, text, *args, **kwargs):
    return _REAL_BOT_REPLY_TO(message, _premium_text_payload(text), *args, **kwargs)

def _bot_edit_message_text_premium(text, *args, **kwargs):
    return _REAL_BOT_EDIT_MESSAGE_TEXT(_premium_text_payload(text), *args, **kwargs)

def _bot_send_photo_premium(chat_id, photo, *args, **kwargs):
    kwargs = _premiumize_caption_kwargs(kwargs)
    return _REAL_BOT_SEND_PHOTO(chat_id, photo, *args, **kwargs)

def _bot_send_video_premium(chat_id, video, *args, **kwargs):
    kwargs = _premiumize_caption_kwargs(kwargs)
    return _REAL_BOT_SEND_VIDEO(chat_id, video, *args, **kwargs)

bot.send_message = _bot_send_message_premium
bot.reply_to = _bot_reply_to_premium
bot.edit_message_text = _bot_edit_message_text_premium
bot.send_photo = _bot_send_photo_premium
bot.send_video = _bot_send_video_premium

# DB LAYER
conn = sqlite3.connect(DB_PATH, check_same_thread=False)
conn.row_factory = sqlite3.Row
conn.execute("PRAGMA journal_mode=WAL;")
conn.execute("PRAGMA synchronous=NORMAL;")
conn.execute("PRAGMA busy_timeout=8000;")
conn.execute("PRAGMA wal_autocheckpoint=2000;")  # ~8MB при page_size=4096

def integrity_ok(c: sqlite3.Connection) -> bool:
    try:
        r = c.execute("PRAGMA integrity_check;").fetchone()
        return bool(r and (r[0] == "ok" or r[0] == "OK"))
    except Exception:
        return False
with DB_LOCK:
    try:
        conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
    except Exception:
        pass

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
    with DB_LOCK:
        c = conn.cursor()
        try:
            c.execute(sql, params)
            rc = c.rowcount
            if commit:
                conn.commit()
            return rc
        finally:
            try: c.close()
            except Exception: pass

def table_exists(name: str) -> bool:
    try:
        r = db_one("SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1", (str(name),))
        return bool(r)
    except Exception:
        return False

# демоны
def _checkpoint_daemon():
    while True:
        time.sleep(1800)  # раз в 30 минут
        with DB_LOCK:
            try:
                conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
            except Exception:
                pass

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

            purge_deleted_db(now)

        except Exception as e:
            send_error_report("_tz3_housekeeping_daemon", e)

        time.sleep(60)

# DB
def init_db():
    db_exec("""
    CREATE TABLE IF NOT EXISTS users (
        user_id     INTEGER PRIMARY KEY,
        username    TEXT,
        first_name  TEXT,
        last_name   TEXT,
        notify_chat_id INTEGER DEFAULT 0,
        notify_off     INTEGER DEFAULT 0,
        last_seen   INTEGER DEFAULT 0
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
    CREATE TABLE IF NOT EXISTS report_state (
        user_id     INTEGER PRIMARY KEY,
        category    TEXT NOT NULL DEFAULT '',
        stage       TEXT NOT NULL DEFAULT '',
        created_ts  INTEGER NOT NULL DEFAULT 0
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

    # миграции users
    for sql in (
        "ALTER TABLE users ADD COLUMN notify_chat_id INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN notify_off INTEGER DEFAULT 0",
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

    db_exec("""
    CREATE TABLE IF NOT EXISTS chat_members (
        chat_id   INTEGER NOT NULL,
        user_id   INTEGER NOT NULL,
        username  TEXT,
        last_seen INTEGER NOT NULL,
        PRIMARY KEY(chat_id, user_id)
    );
    """, commit=True)

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
        "Команда <code>Био восстановить лабу</code>\n"
        f"Для отслеживания состояния лаборатории перейдите в {_bot_pm_link_html()}"
    )

def kb_lab_delete_confirm(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
    kb.row(
        _ikb("Да, подтверждаю", callback_data=f"{CB_LAB_DELETE_OK}:{int(uid)}", style="danger"),
        _ikb("Отмена", callback_data=f"{CB_LAB_DELETE_CANCEL}:{int(uid)}", style="success")
    )
    return kb

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

def _insert_row_into_table(table_name: str, row_data: dict):
    if not row_data:
        return
    cols = list(row_data.keys())
    ph = ",".join(["?"] * len(cols))
    sql = f"INSERT OR REPLACE INTO {table_name}({','.join(cols)}) VALUES ({ph})"
    db_exec(sql, tuple(row_data[c] for c in cols), commit=False)

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
        INSERT INTO users(user_id, username, first_name, last_name, last_seen)
        VALUES(?,?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            username=excluded.username,
            first_name=excluded.first_name,
            last_name=excluded.last_name,
            last_seen=excluded.last_seen
    """, (
        int(tg_user.id),
        (tg_user.username or "").lower() if tg_user.username else None,
        tg_user.first_name,
        tg_user.last_name,
        now_ts()
    ), commit=True)

def touch_user(user_id: int):
    db_exec("UPDATE users SET last_seen=? WHERE user_id=?", (now_ts(), int(user_id)), commit=True)

def ensure_creator_is_support():
    db_exec("""
        INSERT INTO support_agents(user_id, role, added_by, added_at)
        VALUES(?,?,?,?)
        ON CONFLICT(user_id) DO NOTHING
    """, (int(CREATOR_ID), "support", int(CREATOR_ID), now_ts()), commit=True)

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
    c1, _ = get_user_corp(int(viewer_id))
    c2, _ = get_user_corp(int(target_id))
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
    text = f"📄 Игрок {user_tag} покинул Корпорацию."

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
            f"📄 Вы были исключены из Корпорации {corp_name_display(corp_row['name'])}.",
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

    if s_ar < res_amount or s_am < mat_amount:
        return False, "📝 У вас нет столько био-ресурсов или био-материалов."

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
        return corp_by_name(name)

    if message.reply_to_message and getattr(message.reply_to_message, "from_user", None):
        ru = message.reply_to_message.from_user
        if not bool(getattr(ru, "is_bot", False)):
            rcid, _ = get_user_corp(int(ru.id))
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
    text = f"📑 Игрок {joined_tag} вступил в Корпорацию."

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
        return "владельцем"
    if role == "deputy":
        return "заместителем"
    return "участником"

def _corp_request_texts(req_row, actor_id: int, approved: bool) -> tuple[str, str]:
    user_tag = _corp_actor_tag(int(req_row["user_id"]))

    if approved:
        manager_text = f"📑 Игрок {user_tag} вступил в Корпорацию"
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
        return False, "📑 Решение по заявке могут принимать только владелец и заместители."

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
        return "Владелец "
    if role == "deputy":
        return "Заместитель "
    return ""

def _corp_invite_chat_text(corp_row, invited_id: int, inviter_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    inviter_tag = _corp_actor_tag(int(inviter_id))
    prefix = _corp_inviter_prefix(int(corp_row["corp_id"]), int(inviter_id))
    return (
        f"✉️ {invited_tag}, минуточку внимания. "
        f"{prefix}{inviter_tag} пригласил Вас в Корпорацию {corp_name_display(corp_row['name'])}"
    )

def _corp_invite_accept_text(corp_row, invited_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    return (
        f"✅ Игрок {invited_tag} вступил в Корпорацию {corp_name_display(corp_row['name'])}.\n"
        "Встречайте новичка."
    )

def _corp_invite_reject_text(corp_row, invited_id: int) -> str:
    invited_tag = _corp_actor_tag(int(invited_id))
    return (
        f"❌ Игрок {invited_tag} отказался вступать в Корпорацию {corp_name_display(corp_row['name'])}."
    )

def _corp_invite_notify_accept(corp_row, inviter_id: int, invited_id: int):
    corp_id = int(corp_row["corp_id"])
    inviter_tag = _corp_actor_tag(int(inviter_id))
    invited_tag = _corp_actor_tag(int(invited_id))
    prefix = _corp_inviter_prefix(corp_id, int(inviter_id))
    text = (
        f"📄 {prefix}{inviter_tag} пригласил игрока {invited_tag} "
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

    return True, "❎ Приглашение отклонено."

def kb_corp_info(corp_id: int, viewer_id: int, is_member: bool) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)

    if is_member:
        kb.add(InlineKeyboardButton("Участники", callback_data=f"{CORPUI_TAG}:M:{int(corp_id)}:{int(viewer_id)}", style="primary"))

        role = corp_role(int(corp_id), int(viewer_id))
        corp = corp_by_id(int(corp_id))
        if corp and role in ("owner", "deputy"):
            if corp_is_open_value(corp) == 1:
                kb.add(InlineKeyboardButton("Закрыть корпу", callback_data=f"{CORPUI_TAG}:C:{int(corp_id)}:{int(viewer_id)}"))
            else:
                kb.add(InlineKeyboardButton("Открыть корпу", callback_data=f"{CORPUI_TAG}:O:{int(corp_id)}:{int(viewer_id)}"))
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
    sum_be, sum_inf = corp_sums(corp_id)

    if owner:
        ou = (owner["username"] or "")
        od = display_name(owner["first_name"] or "", owner["last_name"] or "", ou, int(owner["user_id"]))
        owner_tag = tg_mention(int(owner["user_id"]), od, username=ou)
    else:
        owner_tag = "неизвестно"

    dep_tags = []
    for d in deputies:
        du = (d["username"] or "")
        dd = display_name(d["first_name"] or "", d["last_name"] or "", du, int(d["user_id"]))
        dep_tags.append(tg_mention(int(d["user_id"]), dd, username=du))

    lines = []
    lines.append(f"🏢 Досье корпорации {corp_name_display(name)}")
    lines.append(f"🧑‍✈️ Владелец: {owner_tag}")
    if dep_tags:
        if len(dep_tags) == 1:
            lines.append(f"🧑‍💼 Заместитель: {dep_tags[0]}")
        else:
            lines.append(f"🧑‍💼 Заместители: " + ", ".join(dep_tags))
    lines.append("")
    lines.append(f"🏷️ Тип корпорации: {'Открытый' if is_open == 1 else 'Закрытый'}")
    if min_be > 0:
        lines.append(f"Порог вступления: {_fmt_k(min_be)}")
    lines.append("")
    lines.append(f"☣️ Био-опыт: {_fmt_k(sum_be)}")
    lines.append(f"🤧 Заражённых: {_fmt_k(sum_inf)}")

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
        "SELECT MIN(COALESCE(NULLIF(TRIM(i.pathogen_name),''), 'неизвестный патоген')) AS pname, "
        "COUNT(DISTINCT i.target_id) AS sick "
        "FROM infections i "
        "GROUP BY lower(COALESCE(NULLIF(TRIM(i.pathogen_name),''), 'неизвестный патоген')) "
        "ORDER BY sick DESC, pname COLLATE NOCASE ASC "
        "LIMIT ?",
        (int(limit),)
    ) or []

def _top_disease_rows_chat(chat_id: int, limit: int):
    return db_all(
        "SELECT MIN(COALESCE(NULLIF(TRIM(i.pathogen_name),''), 'неизвестный патоген')) AS pname, "
        "COUNT(DISTINCT i.target_id) AS sick "
        "FROM infections i "
        "JOIN chat_members cm ON cm.user_id=i.target_id AND cm.chat_id=? "
        "JOIN labs l ON l.user_id=i.target_id "
        "WHERE COALESCE(l.lab_active,0)=1 "
        "GROUP BY lower(COALESCE(NULLIF(TRIM(i.pathogen_name),''), 'неизвестный патоген')) "
        "ORDER BY sick DESC, pname COLLATE NOCASE ASC "
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

    lines.append("<blockquote>")
    for i, r in enumerate(rows, 1):
        uid = int(r["user_id"])
        un = (r["username"] or "")
        disp = display_name(r["first_name"] or "", r["last_name"] or "", un, uid)
        tag = tg_mention(uid, disp, username=un)
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

    lines.append("<blockquote>")
    for i, r in enumerate(rows, 1):
        pname = (r["pname"] or "").strip() or "неизвестный патоген"
        lines.append(f"{i}. {h(pname)} | {_fmt_k(int(r['sick'] or 0))} бол")
    lines.append("</blockquote>")
    return "\n".join(lines), kb_top_switch("D", int(chat_id), int(limit))

def render_top_corps(limit: int, chat_id: int = 0) -> tuple[str, InlineKeyboardMarkup]:
    rows = _top_corp_rows_chat(int(chat_id), int(limit)) if int(chat_id) != 0 else _top_corp_rows(int(limit))
    title = "🔬ТОП КОРПОРАЦИЙ ЧАТА:" if int(chat_id) != 0 else "🔬ТОП КОРПОРАЦИЙ:"
    lines = [title]

    if not rows:
        lines.append("<blockquote>Нет данных.</blockquote>")
        return "\n".join(lines), kb_top_switch("C", int(chat_id), int(limit))

    lines.append("<blockquote>")
    for i, r in enumerate(rows, 1):
        nm = (r["name"] or "").strip()
        lines.append(f"{i}. {corp_name_display(nm)} | {_fmt_k(int(r['be'] or 0))} опыт | {_fmt_k(int(r['sick'] or 0))} бол")
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
        ORDER BY sa.added_at ASC
    """)

def is_support(user_id: int) -> bool:
    if int(user_id) == int(CREATOR_ID):
        return True
    row = db_one("SELECT 1 FROM support_agents WHERE user_id=? LIMIT 1", (int(user_id),))
    return bool(row)

def can_manage_support(user_id: int) -> bool:
    return int(user_id) == int(CREATOR_ID)

def find_user_id_by_username(username: str) -> Optional[int]:
    username = (username or "").strip().lstrip("@").lower()
    if not username:
        return None

    row = db_one("SELECT user_id FROM users WHERE username=? LIMIT 1", (username,))
    if row:
        return int(row["user_id"])

    row = db_one("SELECT user_id FROM bot_bans WHERE username=? LIMIT 1", (username,))
    if row:
        return int(row["user_id"])

    return None

def add_support_agent(target_id: int, added_by: int, role: str = "support") -> None:
    db_exec("""
        INSERT INTO support_agents(user_id, role, added_by, added_at)
        VALUES(?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            role=excluded.role,
            added_by=excluded.added_by,
            added_at=excluded.added_at
    """, (int(target_id), role, int(added_by), now_ts()), commit=True)

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
        text += f"\nПричина: {h(reason)}"
    return text

def _resolve_admin_target_and_reason(message, parsed: "Parsed"):
    if message.reply_to_message and getattr(message.reply_to_message, "from_user", None):
        u = message.reply_to_message.from_user
        return int(u.id), u, (parsed.args or "").strip()

    args = (parsed.args or "").strip()
    if not args:
        return None, None, ""

    parts = args.split(" ", 1)
    token = parts[0].strip()
    reason = parts[1].strip() if len(parts) > 1 else ""

    target_id = resolve_target_id(token)

    if target_id is None:
        s = token.strip()

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

    if int(target_id) == int(CREATOR_ID) and parsed.cmd == "bot_ban":
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

def get_lab(user_id: int) -> sqlite3.Row:
    ensure_lab_exists(user_id)
    return db_one("SELECT * FROM labs WHERE user_id=?", (int(user_id),))

def set_lab_name(user_id: int, name: Optional[str]):
    db_exec("UPDATE labs SET lab_name=? WHERE user_id=?", (name, int(user_id)), commit=True)

def set_pathogen_name(user_id: int, name: Optional[str]):
    db_exec("UPDATE labs SET pathogen_name=? WHERE user_id=?", (name, int(user_id)), commit=True)

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

def render_settings_text(user_id: int) -> str:
    uid = int(user_id)

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
        notify_txt = "❌"
    elif int(notify_chat_id) != 0:
        notify_txt = h(_get_chat_title_cached(int(notify_chat_id)))
    else:
        notify_txt = "личные сообщения 🔊"

    deleted_row = get_deleted_lab_row(uid)
    cid, _cname, role = _user_corp_role_soft(uid)

    lines = []
    lines.append("⚙️ Параметры")
    lines.append("")
    lines.append("ПРИВАТНЫЕ НАСТРОЙКИ:")
    lines.append(f"💰 Баланс: {bal_txt}")
    lines.append(f"🔬 Досье лаборатории: {lab_txt}")
    lines.append("")
    lines.append("УВЕДОМЛЕНИЯ:")
    lines.append(f"Уведомления: {notify_txt}")

    if int(cid) > 0:
        if role in ("owner", "deputy"):
            corp_notify_txt = "🔊" if corp_notify_enabled(uid) == 1 else "🔇"
        else:
            corp_notify_txt = "—"
        lines.append(f"Корпоративные уведомления: {corp_notify_txt}")

    if deleted_row:
        lines.append(f"⏳ Таймер удаления лабы: {_settings_restore_timer_text(uid)}")

    return "\n".join(lines)

def kb_settings(user_id: int) -> InlineKeyboardMarkup:
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

    notify_chat_id, notify_off = get_notify_prefs(uid)
    if int(notify_off) == 1 and int(notify_chat_id) == 0:
        kb.add(_ikb("Включить уведомления в ЛС", callback_data=_settings_cb(uid, "NPM"), style="success"))
    elif int(notify_chat_id) == 0:
        kb.add(_ikb("Отключить уведомления", callback_data=_settings_cb(uid, "NOFF"), style="danger"))
    else:
        kb.row(
            _ikb("Перевести уведомления в ЛС", callback_data=_settings_cb(uid, "NPM"), style="primary"),
            _ikb("Отключить уведомления", callback_data=_settings_cb(uid, "NOFF"), style="danger")
        )

    _cid, _cname, role = _user_corp_role_soft(uid)
    if role in ("owner", "deputy"):
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
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    upsert_user(message.from_user)

    bot.reply_to(
        message,
        render_settings_text(uid),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb_settings(uid)
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

def kb_report_menu(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=2)
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
        return (
            "Отправьте одним сообщением:\n"
            "1-я строка @username нарушителя\n"
            "со 2-й строки описание проблемы\n\n"
            "Можно прикрепить фото или видео к этому сообщению."
        )

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
        return (
            "Опишите запрос на восстановление лаборатории одним сообщением.\n"
            "Можно приложить фото или видео.\n"
            "Желательно указать, почему требуется восстановление через поддержку."
            f"{extra}"
        )

    if cat == "APPEAL":
        return (
            "Отправьте описание апелляции одним сообщением.\n\n"
            "Можно прикрепить фото или видео к этому сообщению."
        )

    return (
        "Отправьте описание проблемы одним сообщением.\n\n"
        "Можно прикрепить фото или видео к этому сообщению."
    )

def _send_report_to_owner(admin_text: str, media_type: str = "", media_file_id: str = "") -> bool:
    try:
        if media_type and media_file_id:
            if len(admin_text) <= 900:
                if media_type == "photo":
                    bot.send_photo(OWNER_ID, media_file_id, caption=admin_text, parse_mode="HTML")
                else:
                    bot.send_video(OWNER_ID, media_file_id, caption=admin_text, parse_mode="HTML")
            else:
                bot.send_message(OWNER_ID, admin_text, parse_mode="HTML", disable_web_page_preview=True)
                if media_type == "photo":
                    bot.send_photo(OWNER_ID, media_file_id)
                else:
                    bot.send_video(OWNER_ID, media_file_id)
        else:
            bot.send_message(OWNER_ID, admin_text, parse_mode="HTML", disable_web_page_preview=True)
        return True
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
        bot.reply_to(message, "Заполните форму одним сообщением (текст + опционально фото/видео).")
        return True

    if not raw:
        bot.reply_to(message, "Пустое сообщение. Пришлите текст описания, при желании добавив фото или видео.")
        return True

    target_un = ""
    desc = ""

    cat_u = str(cat).upper()
    if cat_u == "USER":
        lines = raw.splitlines()
        if not lines or not lines[0].strip().startswith("@"):
            bot.reply_to(message, "Формат неверный. Первая строка должна быть @username.")
            return True
        target_un = lines[0].strip()
        desc = "\n".join(lines[1:]).strip()
        if not desc:
            bot.reply_to(message, "Добавьте описание проблемы со второй строки.")
            return True
    else:
        desc = raw.strip()

    from_name = user_full_name(message.from_user)
    from_un = (getattr(message.from_user, "username", None) or "").strip()
    from_line = h(from_name) + (f" (@{h(from_un)})" if from_un else "")
    ts_txt = _fmt_ts(now_ts())
    cat_title = REPORT_CATS.get(cat_u, cat_u)

    admin_text = f"Репорт {h(ts_txt)}\nОт {from_line}\nКатегория {h(cat_title)}\n"

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

    ok = _send_report_to_owner(admin_text, media_type=media_type, media_file_id=media_file_id)
    if not ok:
        bot.reply_to(message, "Не удалось отправить репорт. Попробуйте позже.")
        return True

    report_clear_state(uid)

    if cat_u == "RESTORE":
        bot.reply_to(message, "Запрос на восстановление лаборатории отправлен администрации на рассмотрение.")
    else:
        bot.reply_to(message, "Репорт отправлен администратору на рассмотрение. Благодарим вас за поддержку проекта.")
    return True

def handle_report_command(message):
    if message.chat.type != "private":
        bot.reply_to(message, "📑 Эта команда работает только в личных сообщениях бота.")
        return

    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    report_clear_state(uid)

    bot.reply_to(
        message,
        "Выберите категорию запроса:",
        reply_markup=kb_report_menu(uid)
    )

def remember_chat_member(chat_id: int, tg_user):
    upsert_user(tg_user)
    uname = (getattr(tg_user, "username", None) or "").strip().lower() or None
    db_exec(
        "INSERT INTO chat_members(chat_id,user_id,username,last_seen) VALUES(?,?,?,?) "
        "ON CONFLICT(chat_id,user_id) DO UPDATE SET username=excluded.username, last_seen=excluded.last_seen",
        (int(chat_id), int(tg_user.id), uname, now_ts()),
        commit=True
    )

def sync_chat_admins(chat_id: int):
    """
    Пытается получить всех админов чата и записать их в chat_members.
    Работает, если у бота есть право видеть админов (обычно всегда) и чат не скрывает список админов.
    """
    try:
        admins = bot.get_chat_administrators(int(chat_id)) or []
    except Exception:
        return

    for cm in admins:
        try:
            u = getattr(cm, "user", None)
            if u:
                remember_chat_member(int(chat_id), u)
        except Exception:
            pass

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

def resolve_target_from_reply_or_args(message, parsed: Optional["Parsed"]):
    """
    Возвращает (target_id, target_user_obj_or_None).
    При reply — всегда берём user из reply_to_message и сразу фиксируем его.
    При args — поддерживает @username / число / (для группы) chat_members.username.
    """
    if message.reply_to_message and message.reply_to_message.from_user:
        u = message.reply_to_message.from_user
        capture_user_context(message, u)
        return int(u.id), u

    if parsed and parsed.args:
        token = parsed.args.split()[0].strip()
        if token.startswith("@"):
            uname = token.lstrip("@").strip().lower()
            tid = find_user_id_by_username(token)
            if tid is None and message.chat.type in ("group", "supergroup"):
                r = db_one(
                    "SELECT user_id FROM chat_members WHERE chat_id=? AND username=? LIMIT 1",
                    (int(message.chat.id), uname)
                )
                if r:
                    tid = int(r["user_id"])
            return (int(tid), None) if tid is not None else (None, None)
        if token.isdigit():
            return int(token), None

    return None, None

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

def bot_cannot_have(what: str) -> str:
    return f"📑 Как бы вам и мне не хотелось, но бот не может участвовать в игре. У бота не может быть {what}"

def _pat_for_text(name: str) -> str:
    name = (name or "").strip()
    return f"«{h(name)}»" if name else "неизвестным патогеном"

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

def parse_message_as_command(text: str) -> Optional[Parsed]:
    if not text:
        return None

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
        if c in ("owner", "агент"):
            return Parsed(raw=raw, has_prefix_char=True, prefix_char=prefix_char, cmd="owner", args=a)
        if c in ("bot_ban", "bot_unban", "remake_lab"):
            return Parsed(raw=raw, has_prefix_char=True, prefix_char=prefix_char, cmd=c, args=a)
        return None

    t = strip_bio_prefix(t)

    sign = None
    if t.startswith("++"):
        sign = "++"
        t = t[2:].lstrip()
    elif t.startswith(("+", "-")):
        sign = t[0]
        t = t[1:].lstrip()

    low = t.lower()

    # команды лс
    if low in ("settings", "настройки"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="settings", args="")

    if low in ("report", "репорт"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="report", args="")

    if low in ("помощь", "help"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="help", args="")

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

    if t == LAB_DELETE_PHRASE:
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_delete_confirm_phrase", args="")

    # приватные настройки
    if sign in ("+", "-"):
        if low in ("баланс", "мешок", "кошелек", "кошелёк", "кош", "бал", "меш"):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                          cmd=("balance_show" if sign == "+" else "balance_hide"), args="")
        if low in ("лаб", "лаборат", "лаборатория", "лаба"):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                          cmd=("lab_show" if sign == "+" else "lab_hide"), args="")

    if low.startswith("скрыть"):
        if ("баланс" in low) or ("мешок" in low) or ("кошелек" in low) or ("кошелёк" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="balance_hide", args="")
        if ("лаб" in low) or ("лаборат" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="lab_hide", args="")

    if low.startswith("показать"):
        if ("баланс" in low) or ("мешок" in low) or ("кошелек" in low) or ("кошелёк" in low):
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="balance_show", args="")
        if ("лаб" in low) or ("лаборат" in low):
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

    # автоответчик
    if sign in ("+", "-") and low in ("автоответчик", "ао", "заражалка", "автозаражалка", "авто заражалка", "аз"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None,
                      cmd=("autoanswer_on" if sign == "+" else "autoanswer_off"), args="")
    if low in ("автоответчик", "ао", "заражалка", "автозаражалка", "авто заражалка", "аз"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="autoanswer_status", args="")

    # калькулятор
    if low == "к" or low == "калькулятор":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc", args="")
    if low.startswith("калькулятор "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc", args=low.split(" ", 1)[1].strip())
    if low.startswith("к "):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="calc", args=low.split(" ", 1)[1].strip())

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

    if low.startswith(("корп инфо", "корпорация инфо", "икорп", "к инфо", "корп", "досье корп", "досье корпорации")):
        rest = ""
        parts = t.split(" ", 2)
        if len(parts) >= 3:
            rest = parts[2].strip()
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

    if sign == "+" and low in ("зам", "заместитель"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy", args="")

    if sign == "+" and (low.startswith("зам ") or low.startswith("заместитель ")):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_deputy", args=rest)

    if low == "исключить" or low.startswith("исключить "):
        rest = ""
        parts = t.split(" ", 1)
        if len(parts) > 1:
            rest = parts[1].strip()
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_kick", args=rest)

    if low == "покинуть":
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="corp_leave", args="")

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
    if low in ("бтоп", "бстата", "стата", "топ") or low.startswith(("бтоп ", "бстата ", "стата ", "топ ")):
        toks = low.split()

        if len(toks) >= 3 and toks[1] in ("корп", "корпораций", "к") and toks[2] == "чата":
            rest = toks[3] if len(toks) >= 4 and toks[3].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_corps_chat", args=rest)

        if len(toks) >= 2 and toks[1] in ("корп", "корпораций", "к"):
            rest = toks[2] if len(toks) >= 3 and toks[2].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_corps", args=rest)

        if len(toks) >= 3 and toks[1] in ("болезней", "болезни", "б") and toks[2] == "чата":
            rest = toks[3] if len(toks) >= 4 and toks[3].isdigit() else ""
            return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="top_diseases_chat", args=rest)

        if len(toks) >= 2 and toks[1] in ("болезней", "болезни", "б"):
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
    if low == "использовать вакцину" or low.startswith("использовать вакцину"):
        return Parsed(raw=raw, has_prefix_char=False, prefix_char=None, cmd="use_vaccine", args="")

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

    return None

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
    name = display_name(fn, ln, username, uid)
    return tg_mention(uid, name, username=username)

def build_start_text(user) -> str:
    agents = get_support_agents()
    online, offline = split_agents_by_online(agents)

    u_name = user_full_name(user)

    lines = []
    lines.append(f'👋 Приветствуем вас, <b>{h(u_name)}</b>, в {h(BOT_TITLE)}')
    lines.append(f'Я создан на основе старой игры бота <a href="{h(IRIS_BOT_LINK)}">Iris | Чат-менеджер</a> с некоторыми доработками.\n\n')
    lines.append("Что вас интересует?\n")
    lines.append(f'1. <code>Био настройки</code> — более гибкая настройка параметров уведомлений и прочего.\n')
    lines.append(f'2. <code>Био репорт</code> — если заметили, что в моей работе что-то не так, уведомите агентов.\n\n')

    lines.append('👨‍⚕️ <b>Агенты поддержки</b>, которые могут ответить на ваши вопросы')

    if online:
        lines.append("🟢 Онлайн")
        lines.extend([format_agent_line(a) for a in online])
    if offline:
        lines.append("🔘 Оффлайн")
        lines.extend([format_agent_line(a) for a in offline])

    lines.append("")
    lines.append(f'📑 Список всех команд <a href="{h(URL_COMMANDS)}">с их описанием</a>')
    lines.append(f'📑 Чат <a href="{h(URL_SUPPORT_CHAT)}">тех.поддержки</a>')
    lines.append(f'📑 Основной <a href="{h(URL_DEV_CHANNEL)}">канал разработки бота</a>')
    lines.append(f'💬 Для повторного вызова агент-листа, введите <code>.помощь</code>')


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

# RESOLVE TARGETS
def resolve_target_id(token: str) -> Optional[int]:
    """/owner target: @username | tg://user?id=... | user_id. Пользователь должен запускать бота."""
    if not token:
        return None
    s = token.strip()

    def _user_exists(uid: int) -> bool:
        return bool(db_one("SELECT 1 FROM users WHERE user_id=? LIMIT 1", (int(uid),)))

    m = re.search(r"tg://user\?id=(\d+)", s)
    if m:
        uid = int(m.group(1))
        return uid if _user_exists(uid) else None

    if re.fullmatch(r"\d+", s):
        uid = int(s)
        return uid if _user_exists(uid) else None

    if s.startswith("@"):
        return find_user_id_by_username(s)

    return None

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
    if corp_name:
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
        + int(_rget(lab, "acceleration", 1) or 1)
    ) // 3
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
        _ikb_premium_icon_only("⚗️", callback_data=_upg_cb("P", owner_id, "ACC", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")))
    return kb

def kb_lab_sec(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_icon_only("👮", callback_data=_upg_cb("P", owner_id, "REA", 1, "D")),
        _ikb_premium_icon_only("🛰️", callback_data=_upg_cb("P", owner_id, "IDS", 1, "D")),
        _ikb_premium_icon_only("📟", callback_data=_upg_cb("P", owner_id, "IPS", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")))
    return kb

def kb_lab_infected(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_lead("🤒", "Ваши болезни", callback_data=_labui_data(owner_id, "B"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")),
    )
    return kb

def kb_lab_diseases(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_lead("🤧", "Заражённые", callback_data=_labui_data(owner_id, "I"), style="primary"),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")),
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
        InlineKeyboardButton("🤧 Заражённые", callback_data=_labui_data(owner_id, "I")),
        InlineKeyboardButton("🤒 Ваши болезни", callback_data=_labui_data(owner_id, "B")),
    )
    return kb

def kb_lab_dev_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🧪", callback_data=_upg_cb("P", owner_id, "PAT", 1, "D")),
        InlineKeyboardButton("💉", callback_data=_upg_cb("P", owner_id, "VAC", 1, "D")),
        InlineKeyboardButton("⚗️", callback_data=_upg_cb("P", owner_id, "ACC", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")))
    return kb

def kb_lab_sec_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("👮", callback_data=_upg_cb("P", owner_id, "REA", 1, "D")),
        InlineKeyboardButton("🛰️", callback_data=_upg_cb("P", owner_id, "IDS", 1, "D")),
        InlineKeyboardButton("📟", callback_data=_upg_cb("P", owner_id, "IPS", 1, "D")),
    )
    kb.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")))
    return kb

def kb_lab_infected_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🤒 Ваши болезни", callback_data=_labui_data(owner_id, "B")),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")),
    )
    return kb

def kb_lab_diseases_inline(owner_id: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        InlineKeyboardButton("🤧 Заражённые", callback_data=_labui_data(owner_id, "I")),
        InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(owner_id, "D")),
    )
    return kb

def render_lab_dev(owner_id: int) -> str:
    lab, lab_name, corp_name, leader = _lab_owner_bundle(owner_id)
    lines = []
    lines.append(f'🏥 Отдел разработок лаборатории <b>{h(lab_name)}</b>:')
    lines.append(f'Руководитель: {leader}')
    if corp_name:
        lines.append(f'🏢 Корпорация: <b>{h(corp_name)}</b>')
    qual = (
        int(_rget(lab, "total_pathogens", 1) or 1)
        + int(_rget(lab, "total_vaccines", 1) or 1)
        + int(_rget(lab, "acceleration", 1) or 1)
    ) // 3   
    lines.append(f'👨‍🔬 Квалификация учёных: {qual} ур')
    lines.append("")
    lines.append("<i>ХАРАКТЕРИСТИКИ:</i>")
    lines.append(f'🧪 Количество патогенов: {lab["total_pathogens"]}')
    lines.append(f'💉 Количество вакцин: {lab["total_vaccines"]}')
    lines.append(f'⚗️ Ускоренное производство: {_rget(lab,"acceleration",1)} ур')
    return "\n".join(lines)

def render_lab_sec(owner_id: int) -> str:
    lab, lab_name, corp_name, leader = _lab_owner_bundle(owner_id)
    lines = []
    lines.append(f'🏣 Отдел безопасности лаборатории <b>{h(lab_name)}</b>:')
    lines.append(f'Руководитель: {leader}')
    if corp_name:
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

    lines = ["🔬 СПИСОК ЗАРАЖЕННЫХ ВАШИМ ПАТОГЕНОМ:"]
    if not rows:
        lines.append("<blockquote>Нет заражённых.</blockquote>")
        return "\n".join(lines)

    items = []
    for i, r in enumerate(rows, 1):
        tid = int(r["target_id"])

        if tid < 0:
            add = "1"
        else:
            add = int(r["add_bio_res"] or 0)
        
        end_ts = int(r["end_ts"] or 0)
        until = _fmt_date_ddmmyy(end_ts)

        u = get_user_row(tid)
        disp = display_name(u["first_name"] or "", u["last_name"] or "", u["username"] or "", tid) if u else str(tid)
        un = (u["username"] or "") if u else ""
        if tid < 0:
            name = "неизвестный пользователь"
        else:
            name = tg_mention(tid, disp, username=un)

        res_word = _ru_form(add, "био-ресурс", "био-ресурса", "био-ресурсов")
        items.append(f"{i}. {name} | 🧬 {add} {res_word} | до {until}")

    lines.append("<blockquote>")
    lines.extend(items)
    lines.append("</blockquote>")
    return "\n".join(lines)

def render_lab_diseases_list(owner_id: int) -> str:
    rows = db_all(
        "SELECT attacker_id, pathogen_name, end_ts, start_ts FROM infections "
        "WHERE target_id=? ORDER BY start_ts DESC LIMIT 30",
        (int(owner_id),)
    ) or []

    lines = ["🔬 СПИСОК ВАШИХ БОЛЕЗНЕЙ:"]
    if not rows:
        lines.append("<blockquote>Нет активных болезней.</blockquote>")
        return "\n".join(lines)

    items = []
    for i, r in enumerate(rows, 1):
        pname = (r["pathogen_name"] or "").strip()
        disease = f"«{h(pname)}»" if pname else "неизвестный патоген" 
        end_ts = int(r["end_ts"] or 0)
        until = _fmt_date_ddmmyy(end_ts)

        inf_by = "неизвестный пользователь"

        items.append(f"{i}. {inf_by} | {disease} | до {until}")

    lines.append("<blockquote>")
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
        return f"{m_total} минут"
    h = m_total // 60
    m = m_total % 60
    return f"{h} часов {m} минут"

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
    if r < 62:
        return 1
    if r < 79:
        return 2
    if r < 89:
        return 3
    if r < 96:
        return 4
    return 5

# стартовые значения
SYNTH_COOLDOWN_SEC = 4 * 3600 # синтезация кулдаун
FEVER_SEC = 60                 # горячка 1 мин
INF_DAY = 1                    # заражение период 1 день
MAX_FEVER_SEC = 3 * 3600  # максимум горячки 3 часа
VACCINE_PRICE = 1500 # цена вакцины
INF_DURATION_SEC = INF_DAY * 86400 # таймер заражения
FEVER_MAX_SEC = 3 * 3600  # максимум горячки 3 часа
REINFECT_CD_SEC = 6 * 3600     # перезаражение 6 часов

# Константы
CB_BUY_VACCINE = "vac:buy"
CB_USE_VACCINE = "vac:use"
CB_USE_VACCINE_X = "vac:usex"
CB_LAB_DELETE_OK = "labdel:ok"
CB_LAB_DELETE_CANCEL = "labdel:cancel"
LAB_DELETE_PHRASE = "Да, я полностью уверен"
CB_AO_MENU = "ao:menu"
CB_AO_TOGGLE = "ao:toggle"
CB_CORP_JOIN = "corp:join"
CB_CORP_REQ_APPROVE = "corp:req:ok"
CB_CORP_REQ_REJECT = "corp:req:no"
CB_CORP_INV_ACCEPT = "corp:inv:ok"
CB_CORP_INV_REJECT = "corp:inv:no"
#            callback_data
LABUI_TAG = "L"   
BALUI_TAG = "C"
INFUI_TAG = "Z"
UPGUI_TAG = "U"
CORPUI_TAG = "G"
TOPUI_TAG = "T"
SETUI_TAG = "W"
REPORTUI_TAG = "Y"

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
    "чат": "c",
}

INF_CHAT_FILTER_SYNONYMS = {
    "+": "p", "б": "p", "больше": "p",
    "-": "m", "м": "m", "меньше": "m",
}

def _clamp(v: int, lo: int, hi: int) -> int:
    return lo if v < lo else hi if v > hi else v

def infect_success_chance(att_infect: int, tgt_imm: int) -> int:
    return _clamp(50 + (int(att_infect) - int(tgt_imm)), 0, 100)

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

def kb_infect_retry_mass_upg(attacker_id: int, mode: str, chat_filter: str) -> InlineKeyboardMarkup:
    kb = kb_infect_retry_mass(attacker_id, mode, chat_filter)
    kb.row(
        _ikb_premium_lead(
            "🦠",
            "Усилить заразность × 1",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 1, "M", str(mode), str(chat_filter)),
            style="success"
        )
    )
    kb.row(
        _ikb_premium_counter(
            "🦠",
            "× 2",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 2, "M", str(mode), str(chat_filter)),
            style="success"
        ),
        _ikb_premium_counter(
            "🦠",
            "× 3",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 3, "M", str(mode), str(chat_filter)),
            style="success"
        ),
        _ikb_premium_counter(
            "🦠",
            "× 5",
            callback_data=_upg_cb_i("P", attacker_id, "INF", 5, "M", str(mode), str(chat_filter)),
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

        att_exp_row = db_one("SELECT COALESCE(bio_exp,0) AS e FROM labs WHERE user_id=?", (int(attacker_id),))
        att_exp = int(att_exp_row["e"] if att_exp_row else 0)

        base = (
            "SELECT cm.user_id AS uid, COALESCE(l.bio_exp,0) AS be "
            "FROM chat_members cm "
            "LEFT JOIN labs l ON l.user_id = cm.user_id "
            "LEFT JOIN infection_cooldowns ic ON ic.attacker_id=? AND ic.target_id=cm.user_id "
            "WHERE cm.chat_id=? AND cm.user_id!=? "
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

        rows = db_all(base, tuple(params)) or []
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

    rows = db_all(base, tuple(params)) or []
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

    return None

def _resolve_target_from_bot_reply(message, attacker_id: int) -> Optional[int]:
    """
    Reply на сообщение бота: пытаемся определить цель заражения по:
      1) entities/caption_entities (text_mention / text_link / mention)
      2) tg://user?id=... в тексте/подписи
      3) @username в тексте/подписи
    Берём первого найденного, кто НЕ attacker.
    """
    rm = message.reply_to_message
    if not rm:
        return None

    ents = getattr(rm, "entities", None) or getattr(rm, "caption_entities", None) or []
    for e in ents:
        et = getattr(e, "type", "") or ""
        if et == "text_mention":
            u = getattr(e, "user", None)
            if u and getattr(u, "id", None):
                uid = int(u.id)
                if uid != int(attacker_id):
                    return uid

        if et in ("text_link", "url"):
            url = getattr(e, "url", "") or ""
            if (not url) and et == "url":
                try:
                    txt = (getattr(rm, "text", None) or getattr(rm, "caption", None) or "")
                    off = int(getattr(e, "offset", 0) or 0)
                    ln = int(getattr(e, "length", 0) or 0)
                    if ln > 0:
                        url = txt[off:off + ln]
                except Exception:
                    url = ""

            m = re.search(r"tg://user\?id=(\d+)", url)
            if m:
                uid = int(m.group(1))
                if uid != int(attacker_id):
                    return uid

            m2 = re.search(r"https?://t\.me/([A-Za-z0-9_]+)", url)
            if m2:
                uname = m2.group(1).lower()
                uid = find_user_id_by_username("@" + uname)
                if uid is None and message.chat.type in ("group", "supergroup"):
                    r = db_one(
                        "SELECT user_id FROM chat_members WHERE chat_id=? AND username=? LIMIT 1",
                        (int(message.chat.id), uname)
                    )
                    if r:
                        uid = int(r["user_id"])
                if uid is not None and int(uid) != int(attacker_id):
                    return int(uid)

        if et == "mention":
            try:
                txt = (getattr(rm, "text", None) or getattr(rm, "caption", None) or "")
                off = int(getattr(e, "offset", 0) or 0)
                ln = int(getattr(e, "length", 0) or 0)
                if ln > 0:
                    token = txt[off:off + ln]
                    if token.startswith("@"):
                        uname = token[1:].lower()
                        uid = find_user_id_by_username("@" + uname)
                        if uid is None and message.chat.type in ("group", "supergroup"):
                            r = db_one(
                                "SELECT user_id FROM chat_members WHERE chat_id=? AND username=? LIMIT 1",
                                (int(message.chat.id), uname)
                            )
                            if r:
                                uid = int(r["user_id"])
                        if uid is not None and int(uid) != int(attacker_id):
                            return int(uid)
            except Exception:
                pass

    raw = (getattr(rm, "text", None) or getattr(rm, "caption", None) or "")
    for m in re.finditer(r"tg://user\?id=(\d+)", raw):
        uid = int(m.group(1))
        if uid != int(attacker_id):
            return uid

    for m in re.finditer(r"@([A-Za-z0-9_]{5,32})", raw):
        uname = m.group(1).lower()
        uid = find_user_id_by_username("@" + uname)
        if uid is None and message.chat.type in ("group", "supergroup"):
            r = db_one(
                "SELECT user_id FROM chat_members WHERE chat_id=? AND username=? LIMIT 1",
                (int(message.chat.id), uname)
            )
            if r:
                uid = int(r["user_id"])
        if uid is not None and int(uid) != int(attacker_id):
            return int(uid)

    return None

def _parse_infect_request(message, parsed: "Parsed", attacker_id: int) -> dict:
    """
    Возвращает структуру запроса.
    kind="U": фикс-цель (reply/@/id)
    kind="M": массовое по переменной (р/+/-/чат)
    kind="NONE": нет цели (ошибка)
    """
    args = (parsed.args or "").strip()
    toks = args.split() if args else []

    if message.reply_to_message and message.reply_to_message.from_user:
        ru = message.reply_to_message.from_user
        if bool(getattr(ru, "is_bot", False)):
            tid = _resolve_target_from_bot_reply(message, attacker_id)
            if tid is not None:
                cnt = 1
                if toks and toks[0].isdigit():
                    cnt = int(toks[0])
                return {"kind": "U", "target": tid, "count": cnt}
        else:
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

    if toks[0].startswith("@"):
        cnt = 1
        if len(toks) >= 2 and toks[1].isdigit():
            cnt = int(toks[1])
        return {"kind": "U", "token": toks[0], "count": cnt}

    if toks[0].isdigit():
        tok0 = toks[0]
        cand = int(tok0)
        cnt = 1
        if len(toks) >= 2 and toks[1].isdigit():
            cnt = int(toks[1])

        if len(tok0) >= 7:
            return {"kind": "U", "token": tok0, "count": cnt}

        known = False
        try:
            if db_one("SELECT 1 FROM users WHERE user_id=? LIMIT 1", (cand,)):
                known = True
            elif message.chat.type in ("group", "supergroup"):
                if db_one(
                    "SELECT 1 FROM chat_members WHERE chat_id=? AND user_id=? LIMIT 1",
                    (int(message.chat.id), cand)
                ):
                    known = True
        except Exception:
            known = False

        if known:
            return {"kind": "U", "token": tok0, "count": cnt}

        return {"kind": "NONE"}

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

def _roll_pct(pct: float) -> bool:
    try:
        return random.random() * 100.0 < float(pct)
    except Exception:
        return False

def _vaccine_fail_pct(target_id: int) -> int:
    """Шанс провала вакцины из-за тяжести патогена (макс 90%)."""
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

    if heavy <= qual:
        return 0
    pct = (heavy - qual) * 2
    if pct > 90:
        pct = 90
    if pct < 0:
        pct = 0
    return int(pct)

VACCINE_FAIL_TEXT = (
    "🧿 Вакцина не смогла справиться с болезнью. Патоген оказался устойчивее к антителам вакцины.\n"
    "Введите повторную дозу или отлежитесь какое-то время."
)

#           улучшение
SKILL_N1 = {
    "INF": 7,   # заразность
    "LET": 4,   # летальность
    "HEA": 12,   # тяжесть
    "IMM": 7,   # иммунитет
    "REA": 6,   # реагирование
    "IDS": 5,   # обнаружение
    "IPS": 7,   # предотвращение
    "ACC": 5,   # ускорение
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
    "ACC": {"col": "acceleration","title_1": "Улучшение лабораторного оборудования", "title_2": "ускорение", "emoji": "⚗️"},
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
    add = (level + 1) * level * (level - 1) * (level - 2) // 24
    return int(n1) + int(add)

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
    if src not in ("C", "D", "I"):
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
        if info["src"] not in ("C", "D", "I"):
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
    return kb

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
            extra_lines += f"🧪: {_format_hms(bp)} → {_format_hms(ap)}\n"
        if bv != av:
            extra_lines += f"💉: {_format_hms(bv)} → {_format_hms(av)}\n"

    return (
        f"{skill['emoji']} {h(skill['title_1'])} на {steps} ур ({final_lvl})\n"
        f"{extra_lines}"
        f"🏷️ Цена: 🧬 <b>{_ru_dots(price)}</b> ({_fmt_k(price)})\n\n"
        f"💬 Чтобы подтвердить усиление навыка, введите команду <code>Био ++{h(skill['title_2'])} {steps}</code>"
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
            extra_lines += f"🧪: {_format_hms(bp)} → {_format_hms(ap)}\n"
        if bv != av:
            extra_lines += f"💉: {_format_hms(bv)} → {_format_hms(av)}\n"

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
        _emit(txt, reply_markup=kb_upgrade(uid, code, steps, "C"))
    else:
        _emit(txt, reply_markup=None)

def handle_calc_command(message, parsed: Parsed):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    parts = (parsed.args or "").strip().split()
    if len(parts) < 3:
        bot.reply_to(
            message,
            disable_web_page_preview=True
        )
        return

    code = _resolve_skill(parts[0])
    if not code or code not in SKILLS:
        return

    try:
        n1 = int(parts[1])
        n2 = int(parts[2])
    except Exception:
        return

    cost = _calc_cost_range(SKILL_N1[code], n1, n2)
    skill = SKILLS[code]

    bot.reply_to(
        message,
        f"🧮 Калькулятор: {skill['emoji']} {h(skill['title_1'])} <b>{n1}</b> → <b>{n2}</b>\n"
        f"Стоимость 🧬 <b>{_ru_dots(cost)}</b> ({_fmt_k(cost)})",
        disable_web_page_preview=True
    )

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

        if action == "P":
            txt = _build_upgrade_preview(uid, code, steps)
            rm = kb_upgrade(uid, code, steps, src, ictype=ictype, ictx=ictx)

            if src == "D":
                rm.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D")))

            _edit(txt, reply_markup=rm)
            bot.answer_callback_query(cq.id)
            return

        ok, txt, _ = _execute_upgrade(uid, code, steps)

        rm = None
        if ok:
            rm = kb_upgrade(uid, code, steps, src, ictype=ictype, ictx=ictx)

            if src == "D":
                rm.row(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D")))

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
            if src == "D":
                rm = InlineKeyboardMarkup()
                rm.add(InlineKeyboardButton("Вернуться к досье", callback_data=_labui_data(uid, "D")))
            else:
                rm = None

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
        "SELECT COALESCE(all_bio_res,0) AS r, COALESCE(all_bio_mater,0) AS m FROM labs WHERE user_id=?",
        (int(user_id),),
    )
    all_bio_res = int(row["r"] if row else 0)
    all_bio_mater = int(row["m"] if row else 0)

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

    return (
        f"Баланс <b>{who}</b>:\n"
        f"🧬 {_fmt_k(all_bio_res)} {res_word}\n"
        f"💊 {_fmt_k(all_bio_mater)} {mat_word}\n"
        f"💬 Запасы можно пополнить командой <code>Синтез</code>"
    )

def _balui_data(uid: int, act: str) -> str:
    return f"{BALUI_TAG}:{int(uid)}:{act}"

def _balui_parse(data: str):
    try:
        p = (data or "").split(":")
        if len(p) != 3 or p[0] != BALUI_TAG:
            return None, None
        return int(p[1]), p[2]
    except Exception:
        return None, None

def synth_left_seconds(uid: int) -> int:
    ensure_lab_exists(uid)
    row = db_one("SELECT COALESCE(last_synth_ts,0) AS t FROM labs WHERE user_id=?", (int(uid),))
    last_ts = int(row["t"] if row else 0)
    left = (last_ts + SYNTH_COOLDOWN_SEC) - now_ts()
    return int(left) if left > 0 else 0

def kb_balance_self(uid: int) -> Optional[InlineKeyboardMarkup]:
    if synth_left_seconds(uid) > 0:
        return None
    kb = InlineKeyboardMarkup()
    kb.add(_ikb_premium_counter("⚗️", "Синтез", callback_data=_balui_data(uid, "S")))
    return kb

def kb_synth(uid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.add(InlineKeyboardButton("Баланс", callback_data=_balui_data(uid, "B")))
    return kb

def synth_attempt(uid: int) -> str:
    """Возвращает текст синтеза (успех или кулдаун)."""
    ensure_lab_exists(uid)
    now = now_ts()

    row = db_one("SELECT COALESCE(last_synth_ts,0) AS t FROM labs WHERE user_id=?", (uid,))
    last_ts = int(row["t"] if row else 0)
    left = (last_ts + SYNTH_COOLDOWN_SEC) - now
    if left > 0:
        return f"❌ СИНТЕЗ НЕ ВЫПОЛНЕН! Ограничение раз в 4 часа. Следующая добыча через {_format_duration(left)}"

    stat_bio_mater = random.randint(1, 100) # синтез старт число
    cof_rost = _pick_cof_rost()
    bio_mater = int(stat_bio_mater * cof_rost)

    db_exec(
        "UPDATE labs SET all_bio_mater=COALESCE(all_bio_mater,0)+?, last_synth_ts=? WHERE user_id=?",
        (bio_mater, now, uid),
        commit=True
    )

    return (
        f"⚗️ СИНТЕЗ ЗАВЕРШЁН! Получено 💊 +{bio_mater} = {stat_bio_mater}×{cof_rost}\n\n"
        f"🔺Коэфициент роста: {cof_rost}"
    )

def handle_synth_command(message):
    uid = int(message.from_user.id)
    upsert_user(message.from_user)
    ensure_lab_exists(uid)

    text = synth_attempt(uid)
    bot.reply_to(message, text, reply_markup=kb_synth(uid), disable_web_page_preview=True)

#             вакцина
def get_fever_and_vaccines(user_id: int) -> tuple[int, str, int]:
    ensure_lab_exists(user_id)
    r = db_one(
        "SELECT COALESCE(fever_until_ts,0) AS f, COALESCE(fever_pathogen,'') AS fp, COALESCE(ready_vaccines,0) AS v "
        "FROM labs WHERE user_id=?",
        (int(user_id),)
    )
    if not r:
        return 0, "", 0
    return int(r["f"] or 0), (r["fp"] or ""), int(r["v"] or 0)

VACCINE_FAIL_TEXT = (
    "🧿 Вакцина не смогла справиться с болезнью. Патоген оказался устойчивее к антителам вакцины.\n"
    "Введите повторную дозу или отлежитесь какое-то время."
)

def _vaccine_fail_pct(target_id: int) -> int:
    """
    Шанс провального срабатывания вакцины (макс 90%):
    за каждый 1% уровня тяжести свыше квалификации +2%.
    Здесь "тяжесть" берём как MAX heaviness среди активных инфекций на цели.
    """
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

    if heavy <= qual:
        return 0

    pct = (heavy - qual) * 2
    if pct > 90:
        pct = 90
    if pct < 0:
        pct = 0
    return int(pct)

def kb_vaccine_retry() -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup()
    kb.row(
        _ikb_premium_counter("💉", "× 1", callback_data=f"{CB_USE_VACCINE_X}:1"),
        _ikb_premium_counter("💉", "× 5", callback_data=f"{CB_USE_VACCINE_X}:5"),
        _ikb_premium_counter("💉", "× 10", callback_data=f"{CB_USE_VACCINE_X}:10"),
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

            need = VACCINE_PRICE
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
                "❗Для более корректной работы команд, рекомендую выдать мне приписку администратора. Права администратора выдавать не обязательно.\n\n"
                f'Остались вопросы? Можете обратиться в <a href="{h(URL_SUPPORT_CHAT)}">наш официальный чат</a>'
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
    - В группе/супергруппе: если бота удалили/он вышел — сбрасываем notify_chat_id всем, кто был привязан к этому чату
    """
    try:
        chat = getattr(update, "chat", None)
        if not chat:
            return

        chat_id = int(getattr(chat, "id", 0) or 0)
        chat_type = (getattr(chat, "type", "") or "").lower()

        new_cm = getattr(update, "new_chat_member", None)
        status = (getattr(new_cm, "status", "") or "").lower() if new_cm else ""

        if chat_type in ("group", "supergroup") and status in ("left", "kicked"):
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

        if chat_type == "private":
            fake_user = type("U", (), {})()
            fake_user.id = chat_id
            fake_user.username = None
            fake_user.first_name = None
            fake_user.last_name = None
            upsert_user(fake_user)

    except Exception as e:
        send_error_report("on_my_chat_member_update", e)

# CALLBACK HANDLERS
@bot.callback_query_handler(func=lambda cq: (cq.data or "") == CB_BUY_VACCINE)
def cb_buy_vaccine(cq):
    try:
        uid = int(cq.from_user.id)
        upsert_user(cq.from_user)

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
            rm.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=CB_USE_VACCINE))
            text = (
                "💉 У вас нет необходимости покупать вакцину. Для быстрого выздоровления используйте вакцину\n"
                "команда <code>Био использовать вакцину</code>"
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
            text = "📝 У вас недостаточно средств."
        elif status == "FAIL":
            text = VACCINE_FAIL_TEXT
            rm = kb_vaccine_retry()
        else:
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
    except Exception as e:
        send_error_report("cb_buy_vaccine", e)
        try:
            bot.answer_callback_query(cq.id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda cq: (cq.data or "") == CB_USE_VACCINE)
def cb_use_vaccine(cq):
    try:
        uid = int(cq.from_user.id)
        upsert_user(cq.from_user)

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
                rm = kb_vaccine_retry()
            elif status == "NO_VACCINE":
                price_txt = _fmt_bio_res(VACCINE_PRICE)
                text = (
                    "💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: "
                    f"{price_txt}, команда <code>Био купить вакцину</code>"
                )
                rm = InlineKeyboardMarkup()
                rm.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=CB_BUY_VACCINE))
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
        upsert_user(cq.from_user)

        doses = 1
        try:
            doses = int((cq.data or "").split(":", 2)[2])
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
                rm = kb_vaccine_retry()
            elif status == "NO_VACCINE":
                price_txt = _fmt_bio_res(VACCINE_PRICE)
                text = prefix + (
                    "💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: "
                    f"{price_txt}, команда <code>Био купить вакцину</code>"
                )
                rm = InlineKeyboardMarkup()
                rm.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=CB_BUY_VACCINE))
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
        uid, act = _balui_parse(cq.data or "")
        if uid is None:
            bot.answer_callback_query(cq.id)
            return

        if int(cq.from_user.id) != int(uid):
            bot.answer_callback_query(cq.id)
            return

        if act == "S":
            text = synth_attempt(uid)
            rm = kb_synth(uid)
        elif act == "B":
            text = render_balance(uid)
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
                bot.answer_callback_query(cq.id, "У вас нет активной Лаборатории.", show_alert=True)
                return

            if act == "HB":
                set_hide_balance(int(uid), not bool(int(lab_row["hb"] or 0)))
            else:
                set_hide_lab(int(uid), not bool(int(lab_row["hl"] or 0)))

        elif act == "NPM":
            set_notify_prefs(int(uid), 0, 0)

        elif act == "NOFF":
            set_notify_prefs(int(uid), 0, 1)

        elif act == "CN":
            _cid, _cname, role = _user_corp_role_soft(int(uid))
            if role not in ("owner", "deputy"):
                bot.answer_callback_query(cq.id, "Корпоративные уведомления доступны только владельцу и заместителям.", show_alert=True)
                return
            cur = corp_notify_enabled(int(uid))
            set_corp_notify_enabled(int(uid), 0 if cur == 1 else 1)

        else:
            bot.answer_callback_query(cq.id)
            return

        text = render_settings_text(int(uid))
        rm = kb_settings(int(uid))

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

        if act == "RESTORE" and not get_deleted_lab_row(int(uid)):
            bot.answer_callback_query(cq.id, "У вас нет сохранённой лаборатории для восстановления.", show_alert=True)
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

        if cq.message:
            limited_edit_message_text(
                text=text,
                chat_id=cq.message.chat.id,
                msg_id=cq.message.message_id,
                parse_mode="HTML",
                reply_markup=None,
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

# COMANDS HANDLERS
def handle_owner_command(message, parsed: Parsed):
    if not parsed.has_prefix_char or parsed.cmd != "owner":
        return

    upsert_user(message.from_user)

    if not can_manage_support(message.from_user.id):
        bot.reply_to(message, "📑 Ваш ранг не позволяет назначять агентов технической поддержки.")
        return

    if not parsed.args:
        return

    target_id = resolve_target_id(parsed.args)
    if target_id is None:
        return

    if parsed.args.strip().startswith("@"):
        if target_id is None:
            return

    add_support_agent(target_id, added_by=message.from_user.id, role="support")
    ensure_lab_exists(target_id)

    row = get_user_row(target_id)
    disp = display_name(row["first_name"] or "", row["last_name"] or "", row["username"] or "", target_id) if row else str(target_id)
    un = (row["username"] or "") if row else ""
    bot.reply_to(
        message,
        f"✅ Пользователь <b>{tg_mention(target_id, disp, username=un)}</b> назначен агентом технической поддержки.", disable_web_page_preview=True,
    )

def handle_infect_command(message, parsed: Parsed, edit_ctx: Optional[dict] = None, actor_user=None):
    actor = actor_user or message.from_user
    attacker_id = int(actor.id)
    upsert_user(actor)
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
            """Отправка уведомлений о заражении/IDS. Возвращает Message (если удалось отправить)."""
            try:
                notify_chat_id, notify_off = get_notify_prefs(int(tid))
                if int(notify_off) == 1 and int(notify_chat_id) == 0:
                    return None
    
                dest = int(notify_chat_id) if int(notify_chat_id) != 0 else int(tid)
                try:
                    return bot.send_message(dest, text, parse_mode="HTML", disable_web_page_preview=True)
                except Exception:
                    if int(notify_chat_id) != 0:
                        try:
                            set_notify_prefs(int(tid), 0, 0)
                            try:
                                bot.send_message(int(tid),
                                    "⚠️ Не удалось отправить уведомление в привязанный чат. Привязка сброшена на личные сообщения.",
                                    disable_web_page_preview=True)
                            except Exception:
                                pass
                        except Exception:
                            pass
    
                    if int(dest) != int(tid):
                        try:
                            return bot.send_message(int(tid), text, parse_mode="HTML", disable_web_page_preview=True)
                        except Exception:
                            return None
                return None
            except Exception:
                return None

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
            kb.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=CB_USE_VACCINE))
            _emit(
                f"🌡️ У вас горячка, вызванная {_pat_for_fever(fever_pat)}. Придётся отлежаться, пока она не пройдёт\n"
                f"Время выздоровления {_format_hms(left)}"
                f"\n\n💉 Для быстрого выздоровления используйте вакцину\n"
                f"команда <code>Био использовать вакцину</code>",
                reply_markup=kb
            )
        else:
            price_txt = _fmt_bio_res(VACCINE_PRICE)
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=CB_BUY_VACCINE))
            _emit(
                f"🌡️ У вас горячка, вызванная {_pat_for_fever(fever_pat)}. Придётся отлежаться, пока она не пройдёт\n"
                f"Время выздоровления {_format_hms(left)}"
                f"\n\n💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: {price_txt}, "
                f"команда <code>Био купить вакцину</code>",
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
            _ikb_premium_counter("⚗️", "× 1", callback_data=cb_acc_1),
            _ikb_premium_counter("⚗️", "× 2", callback_data=cb_acc_2),
            _ikb_premium_counter("⚗️", "× 5", callback_data=cb_acc_5),
        )

        _emit(
            "📝 Закончились все патогены\n"
            f"⏱️ Новый через {_format_hms(npi)} ({eta})\n"
            f"🧪 Ячеек для патогенов: {total_pathogens} | +1 = {pat_price_line}\n"
            f"👨‍🔬 Квалификация учёных: {qual} ур ({_format_hm_from_seconds(craft_sec)})\n"
            "💬 Вы также можете заказать дополнительные ячейки с патогенами в лабораторию командой "
            "<code>Био +патоген</code> + количество необходимых ячеек",
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
            if token.startswith("@"):
                uname = token.lstrip("@").strip().lower()
                target_id = find_user_id_by_username(token)
                if target_id is None and message.chat.type in ("group", "supergroup"):
                    r = db_one(
                        "SELECT user_id FROM chat_members WHERE chat_id=? AND username=? LIMIT 1",
                        (int(message.chat.id), uname)
                    )
                    if r:
                        target_id = int(r["user_id"])
            elif token.isdigit():
                target_id = int(token)

        if target_id is None:
            _emit("📑 Цель для заражения не найдена.")
            return

        if is_bot_target(target_id, target_user_obj, token):
            _emit("📑 Объект заражения не подвержен заражению. Вы не можете заразить бота.")
            return
        if int(target_id) == int(attacker_id):
            _emit("🧪 Вы не можете заразить самого себя.")
            return

        if message.chat.type == "private" and not is_lab_active(int(target_id)):
            _emit(
                "📝 Объект ещё не создал свою лабораторию.\n\n"
                "💬 Вы можете первый раз заразить его только в общей с вами беседе.\n"
                "Либо пригласите его присоединиться к мини-игре «Био-атака», попросив его ввести команду <code>Био лаб</code>"
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

        for i in range(1, cnt + 1):
            used = i
            if random.random() * 100.0 < rand_evt_pct:
                rand_evt = True
                rand_evt_text = pick_random_event_text()
                break

            roll = random.randint(1, 100)
            if roll > p_success:
                immune_fail += 1
                continue
            if roll <= p_success:
                success = True
                texp = int(trow["be"] if trow else 0)
                stolen = (texp // 2)
                if stolen < 1:
                    stolen = 1
                gained = int(stolen)

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
                            "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name) "
                            "VALUES (?,?,?,?,?,?,1,?) "
                            "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                            "start_ts=excluded.start_ts, end_ts=excluded.end_ts, add_bio_res=excluded.add_bio_res, "
                            "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name",
                            (attacker_id, int(target_id), now, end_ts, gained, next_payout, (pathogen_name or "").strip())
                        )

                        c.execute(
                            "INSERT INTO infection_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
                            "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
                            (attacker_id, int(target_id), now + REINFECT_CD_SEC)
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
                            res_word = _ru_form(int(gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                            target_notice += (
                                "\n\n👨‍🔬 Вы ещё не подвергались заражению этим патогеном, поэтому каждый день, пока вы заражены, "
                                f"игрок будет получать по {int(gained)} {res_word}"
                            )
                        
                        att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
                        tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
                        
                        if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                            exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
                            result_text = (
                                f"🦠 {organizer_tag} подверг заражению {_pat_for_text((pathogen_name or '').strip())} {target_tag}\n"
                                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                                f"🤒 Заражение на {_format_days(inf_days)}\n"
                                f"☣️ +{_fmt_k(int(gained))} {exp_word}"
                            )
                            if first_time:
                                res_word = _ru_form(int(gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                                result_text += (
                                    "\n\n👨‍🔬 Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, "
                                    f"вы будете получать по {int(gained)} {res_word}"
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

        ur = get_user_row(int(target_id))
        tgt_disp = display_name(ur["first_name"] or "", ur["last_name"] or "", ur["username"] or "", int(target_id)) if ur else str(target_id)
        tgt_un = (ur["username"] or "") if ur else ""
        target_tag = tg_mention(int(target_id), tgt_disp, username=tgt_un)

        pat_txt = f"«{h(pathogen_name.strip())}»" if (pathogen_name or "").strip() else "неизвестным патогеном"

        header = ""
        if cnt > 1:
            header = (
                "📋 Отчёт об операции заражения объекта:\n"
                f"Использовано патогенов: {used}\n\n"
            )

        if not success:
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
                    conn.commit()
                except Exception:
                    conn.rollback()
                    raise
                finally:
                    try:
                        c.close()
                    except Exception:
                        pass
        
        if rand_evt:
            rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
            rem = int(rem_row["rp"] if rem_row else 0)
            att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
            tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
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
                    autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")
            _emit(
                header +
                f"💢 Попытка заразить «{target_tag}» провалилась...\n"
                f"{h(rand_evt_text)}\n"
                f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_mat_line}",
                reply_markup=kb_infect_retry_user(attacker_id, int(target_id))
            )
            if message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
                reply_mid = 0
                if edit_ctx and isinstance(edit_ctx, dict):
                    reply_mid = int(edit_ctx.get("msg_id") or 0)
                if reply_mid <= 0:
                    reply_mid = int(getattr(message, "message_id", 0) or 0)
                autoanswer_trigger(int(target_id), attacker_id, int(message.chat.id), reply_mid, "CHAT")
            return

        if success:
            txt = (
                header +
                f"🦠 {attacker_tag} подверг заражению {pat_txt} {target_tag}\n"
                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                f"🤒 Заражение на {_format_days(inf_days)}\n"
                f"☣️ +{gained} био-опыт"
            )
            if first_time:
                res_word = _ru_form(int(gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                txt += (
                    "\n\n👨‍🔬 Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, "
                    f"вы будете получать по {int(gained)} {res_word}"
                )
            _emit(txt)
            if message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
                reply_mid = 0
                if edit_ctx and isinstance(edit_ctx, dict):
                    reply_mid = int(edit_ctx.get("msg_id") or 0)
                if reply_mid <= 0:
                    reply_mid = int(getattr(message, "message_id", 0) or 0)
                autoanswer_trigger(int(target_id), attacker_id, int(message.chat.id), reply_mid, "CHAT")
            return
        att_ids_lvl = int(lab_row["a_ids"] if lab_row else 1) or 1
        tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
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
        if message.chat.type in ("group", "supergroup") and _chat_has_user(message.chat.id, int(target_id)):
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

        ensure_lab_exists(int(tid))

        trow = db_one(
            "SELECT COALESCE(immunity,0) AS imm, COALESCE(bio_exp,0) AS be, COALESCE(ids,1) AS t_ids FROM labs WHERE user_id=?",
            (int(tid),)
        )
        tgt_imm = int(trow["imm"] if trow else 0)
        p_success = infect_success_chance(attacker_inf, tgt_imm)
        
        used += 1
        if message.chat.type in ("group", "supergroup") and _chat_has_user(int(message.chat.id), int(tid)):
            reply_mid = 0
            if edit_ctx and isinstance(edit_ctx, dict):
                reply_mid = int(edit_ctx.get("msg_id") or 0)
            if reply_mid <= 0:
                reply_mid = int(getattr(message, "message_id", 0) or 0)
            autoanswer_trigger(int(tid), int(attacker_id), int(message.chat.id), reply_mid, "CHAT")

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
        roll = random.randint(1, 100)

        if roll > p_success:
            fail += 1
            last_tid = int(tid)
            last_success = False
            last_dummy = False
            last_gained = 0
            last_first_time = False
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
                    f"🥽 Иммунитет объекта «{tgt_tag}» оказался стойким к вашему патогену.\n"
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

        texp = int(trow["be"] if trow else 0)
        stolen = (texp // 2)
        if stolen < 1:
            stolen = 1
        gained = int(stolen)
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
                    "INSERT INTO infections(attacker_id,target_id,start_ts,end_ts,add_bio_res,next_payout_ts,counted,pathogen_name) "
                    "VALUES (?,?,?,?,?,?,1,?) "
                    "ON CONFLICT(attacker_id,target_id) DO UPDATE SET "
                    "start_ts=excluded.start_ts, end_ts=excluded.end_ts, add_bio_res=excluded.add_bio_res, "
                    "next_payout_ts=excluded.next_payout_ts, counted=1, pathogen_name=excluded.pathogen_name",
                    (attacker_id, int(tid), now, end_ts, gained, next_payout, (pathogen_name or "").strip())
                )
                c.execute(
                    "INSERT INTO infection_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
                    "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
                    (attacker_id, int(tid), now + REINFECT_CD_SEC)
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
            ur = get_user_row(int(tid))
            tgt_disp = display_name(
                ur["first_name"] or "", ur["last_name"] or "", ur["username"] or "", int(tid)
            ) if ur else str(tid)
            tgt_un = (ur["username"] or "") if ur else ""
            tgt_tag = tg_mention(int(tid), tgt_disp, username=tgt_un)

            notify_chat_id, notify_off = get_notify_prefs(int(tid))
            if not (int(notify_off) == 1 and int(notify_chat_id) == 0):
                notice = (
                    f"🦠 Кто-то подверг заражению {_pat_for_text((pathogen_name or '').strip())} {tgt_tag}\n"
                    f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                    f"🤒 Заражение на {_format_days(inf_days)}"
                )
                if ft:
                    res_word = _ru_form(int(gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                    notice += (
                        "\n\n👨‍🔬 Вы ещё не подвергались заражению этим патогеном, поэтому каждый день, пока вы заражены, "
                        f"игрок будет получать по {int(gained)} {res_word}"
                    )
                tgt_ids_lvl = int(trow["t_ids"] if trow else 1) or 1
                if ids_should_fire(att_ids_lvl, tgt_ids_lvl):
                    exp_word = _ru_form(int(gained), "био-опыт", "био-опыта", "био-опыта")
                    result_text = (
                        f"🦠 {organizer_tag} подверг заражению {_pat_for_text((pathogen_name or '').strip())} {tgt_tag}\n"
                        f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                        f"🤒 Заражение на {_format_days(inf_days)}\n"
                        f"☣️ +{_fmt_k(int(gained))} {exp_word}"
                    )
                    if ft:
                        res_word = _ru_form(int(gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                        result_text += (
                            "\n\n👨‍🔬 Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, "
                            f"вы будете получать по {int(gained)} {res_word}"
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
                else:
                    _notify_target(int(tid), notice)
        except Exception:
            pass

    if used <= 0:
        _emit("📑 Цель для заражения не найдена.")
        return
    
    if cnt == 1 and used == 1:
        att_disp = user_full_name(actor)
        att_un = getattr(actor, "username", "") or ""
        attacker_tag = tg_mention(attacker_id, att_disp, username=att_un)
    
        if last_dummy or (last_tid is None):
            single_target_tag = "неизвестный пользователь"
        else:
            ur = get_user_row(int(last_tid))
            tgt_disp = display_name(
                ur["first_name"] or "", ur["last_name"] or "", ur["username"] or "", int(last_tid)
            ) if ur else str(last_tid)
            tgt_un = (ur["username"] or "") if ur else ""
            single_target_tag = tg_mention(int(last_tid), tgt_disp, username=tgt_un)

        if last_evt:
            rem_row = db_one(
                "SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?",
                (attacker_id,)
            )
            rem = int(rem_row["rp"] if rem_row else 0)
        
            rm = kb_infect_retry_mass(attacker_id, mode, chat_filter)
            if (not last_dummy) and (last_tid is not None):
                rm = kb_infect_retry_user(attacker_id, int(last_tid))

            _emit(
                f"💢 Попытка заразить «{single_target_tag}» провалилась...\n"
                f"{h(last_evt_text)}\n"
                f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_mat_line}",
                reply_markup=rm
            )
            return

        if last_success:
            bio_word = _ru_form(last_gained, "био-опыт", "био-опыта", "био-опыта")
            txt = (
                f"🦠 {attacker_tag} подверг заражению {_pat_for_text((pathogen_name or '').strip())} {single_target_tag}\n"
                f"☠️ Горячка на {_format_hm_from_seconds(fever_add)}\n"
                f"🤒 Заражение на {_format_days(inf_days)}\n"
                f"☣️ +{last_gained} {bio_word}"
            )
            if last_first_time or last_dummy:
                res_word = _ru_form(int(last_gained), "био-ресурс", "био-ресурса", "био-ресурсов")
                txt += (
                    "\n\n👨‍🔬 Объект ещё не подвергался заражению вашим патогеном, поэтому каждый день, пока он заражён, "
                    f"вы будете получать по {int(last_gained)} {res_word}"
                )
            _emit(txt)
            return
    
        rem_row = db_one("SELECT COALESCE(ready_pathogens,0) AS rp FROM labs WHERE user_id=?", (attacker_id,))
        rem = int(rem_row["rp"] if rem_row else 0)
        _emit(
            f"🥽 Иммунитет объекта «{single_target_tag}» оказался стойким к вашему патогену.\n"
            "Антитела смогли справиться с заражением.\n"
            f"🧪 Осталось патогенов: {rem} | +1 = {pat_price_txt}",
            reply_markup=(
                kb_infect_retry_user_upg(attacker_id, int(last_tid))
                if ((not last_dummy) and (last_tid is not None))
                else kb_infect_retry_mass_upg(attacker_id, mode, chat_filter)
            )
        )
        
        if message.chat.type in ("group", "supergroup") and last_tid and last_tid > 0 and _chat_has_user(message.chat.id, int(last_tid)):
            reply_mid = 0
            if edit_ctx and isinstance(edit_ctx, dict):
                reply_mid = int(edit_ctx.get("msg_id") or 0)
            if reply_mid <= 0:
                reply_mid = int(getattr(message, "message_id", 0) or 0)
            autoanswer_trigger(int(last_tid), attacker_id, int(message.chat.id), reply_mid, "CHAT")
        return

    txt = (
        "📋 Отчёт об операции массового заражения объектов:\n"
        f"Использовано патогенов: {used}\n\n"
        f"🦠 Успешно заражено: {succ}\n"
    )
    if first_cnt > 0:
        txt += f"🩻 Заражено впервые: {first_cnt}\n"
    txt += f"❌ Неудачные заражения: {fail}\n"

    if succ > 0:
        bio_word = _ru_form(total_gained, "био-опыт", "био-опыта", "био-опыта")
        txt += f"\n☣️‍ +{_fmt_k(total_gained)} {bio_word}"

    _emit(txt, reply_markup=kb_infect_retry_mass(attacker_id, mode, chat_filter))

def handle_sabotage_command(message, parsed: Parsed, edit_ctx: Optional[dict] = None, actor_user=None):
    actor = actor_user or message.from_user
    attacker_id = int(actor.id)
    upsert_user(actor)
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

    p = a_rea - t_ips
    if p < 0:
        p = 0
    if p > 90:
        p = 90

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
        try:
            notify_chat_id, notify_off = get_notify_prefs(int(tid))
            if int(notify_off) == 1 and int(notify_chat_id) == 0:
                return None

            dest = int(notify_chat_id) if int(notify_chat_id) != 0 else int(tid)
            try:
                return bot.send_message(dest, text, parse_mode="HTML", disable_web_page_preview=True)
            except Exception:
                if int(notify_chat_id) != 0:
                    try:
                        set_notify_prefs(int(tid), 0, 0)
                        try:
                            bot.send_message(int(tid),
                                "⚠️ Не удалось отправить уведомление в привязанный чат. Привязка сброшена на личные сообщения.",
                                disable_web_page_preview=True)
                        except Exception:
                            pass
                    except Exception:
                        pass
                if int(dest) != int(tid):
                    try:
                        return bot.send_message(int(tid), text, parse_mode="HTML", disable_web_page_preview=True)
                    except Exception:
                        return None
            return None
        except Exception:
            return None

    db_exec(
        "INSERT INTO sabotage_cooldowns(attacker_id,target_id,until_ts) VALUES (?,?,?) "
        "ON CONFLICT(attacker_id,target_id) DO UPDATE SET until_ts=excluded.until_ts",
        (attacker_id, int(target_id), int(now + 86400)),
        commit=True
    )

    roll = random.randint(1, 100)
    success = (roll <= p and p > 0)

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

        db_exec(
            "UPDATE labs SET ready_pathogens=?, ready_vaccines=?, next_pathogen_in=?, next_vaccine_in=? WHERE user_id=?",
            (new_rp, new_rv, new_npi, new_nvi, int(target_id)),
            commit=True
        )

        tgt_notice = (
            "💥 В вашу лабораторию совершена диверсия. Марадёры повредили контейнеры с образцами и лабораторное оборудование.\n\n"
            f"🧪 Потеряно патогенов: {lost_p}\n"
            f"💉 Потеряно вакцин: {lost_v}\n"
            f"⏱️ Задержка производства: патоген +{_format_hms(add_p)} | вакцина +{_format_hms(add_v)}\n"
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
                    f"💉 Потеряно вакцин: {lost_v}"
                )
            )
            ids_msg = _notify(int(target_id), ids_text)
            if ids_msg:
                autoanswer_trigger(int(target_id), attacker_id, int(ids_msg.chat.id), int(ids_msg.message_id), "IDS")

        _emit(
            "🥷 Диверсия выполнена.\n"
            f"Цель: «{target_tag}»\n"
            f"✅ Успех ({p}%)\n"
            f"🧪 Уничтожено патогенов: {lost_p}\n"
            f"💉 Уничтожено вакцин: {lost_v}\n"
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
        f"❌ Неудача ({p}%)\n"
        f"🧾 Компенсация ущерба: {spent_txt}\n"
        "⏱️ КД на цель: 24 часа"
    )

def handle_lab_commands(message, parsed: Parsed):
    uid = message.from_user.id
    upsert_user(message.from_user)
    ensure_creator_is_support()

    if parsed.cmd not in ("lab_delete", "restore_lab", "lab_delete_confirm_phrase"):
        ensure_lab_exists(uid)

    if parsed.cmd == "lab_delete":
        if not is_lab_active(int(uid)):
            bot.reply_to(message, "📑 У вас нет активной Лаборатории.")
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

    if parsed.cmd == "lab_delete_confirm_phrase":
        if not has_lab_delete_pending(int(uid)):
            return

        ok, text = _perform_lab_delete(int(uid))
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd == "restore_lab":
        ok, text = _restore_deleted_lab(int(uid), support_mode=False)
        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True)
        return

    if parsed.cmd == "labname":
        if not parsed.args:
            lab = get_lab(uid)
            current = (lab["lab_name"] or "").strip()
            if not current:
                current = default_lab_name(get_user_row(uid), uid)
            bot.reply_to(message, f"🏢 Текущее имя лаборатории: <b>{h(current)}</b>\nЧтобы изменить его, введите:\n <code>Био имя имя лаборатории Название</code>")
            return

        new_name = parsed.args.strip()
        if len(new_name) > 40:
            bot.reply_to(message, "📑 Название вашей лаборатории превышает максимальные 40 символов.")
            return
        set_lab_name(uid, new_name)
        bot.reply_to(message, f"✅ Имя лаборатории успешно изменено!")
        return

    if parsed.cmd == "pathogenname":
        if not parsed.args:
            lab = get_lab(uid)
            current = (lab["pathogen_name"] or "").strip() or "неизвестный патоген"
            bot.reply_to(message, f"🦠 Текущее имя патогена: <b>{h(current)}</b>\nЧтобы изменить его, введите:\n <code>Био имя патогена Название</code>")
            return

        new_name = parsed.args.strip()
        if len(new_name) > 40:
            bot.reply_to(message, "📑 Название вашего патогена превышает максимальные 40 символов.")
            return
        set_pathogen_name(uid, new_name)
        bot.reply_to(message, f"✅ Имя патогена успешно изменено!")
        return

    if parsed.cmd in ("lab", "mylab"):
        mark_lab_active(int(uid))
        _maybe_apply_deleted_lab_bonus(int(uid))
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
        bot.reply_to(message, "📑 Сначала создайте лабораторию. Команда <code>Био лаб</code>.")
        return

    my_cid, my_cname = get_user_corp_resolved(uid)

    if parsed.cmd == "corp_create":
        if my_cid > 0:
            bot.reply_to(message, "📑 Вы уже состоите в Корпорации.")
            return

        name = (parsed.args or "").strip()
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
            bot.reply_to(message, "📄 Приглашение отправлено игроку в личные сообщения.")
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

        bot.reply_to(message, f"✅ Игрок {_corp_actor_tag(int(target_id))} назначен заместителем Корпорации {corp_name_display(corp['name'])}.", parse_mode="HTML", disable_web_page_preview=True)
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
            bot.reply_to(message, "📑 Нельзя исключить самого себя. Используйте команду <code>Био покинуть</code>.", parse_mode="HTML", disable_web_page_preview=True)
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

        bot.reply_to(message, f"✅ Игрок {_corp_actor_tag(int(target_id))} исключён из корпорации.", parse_mode="HTML", disable_web_page_preview=True)
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
            if parsed.cmd == "corp_send_res":
                ok, err = _corp_transfer_apply(int(uid), int(target_id), res_amount=int(amount), mat_amount=0)
                if not ok:
                    bot.reply_to(message, err)
                    return

                word = _ru_form(int(amount), "био-ресурс", "био-ресурса", "био-ресурсов")
                bot.reply_to(
                    message,
                    f"✅Успех. Игроку {_corp_actor_tag(int(target_id))} передано 🧬 {_fmt_k(int(amount))} {word}.",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
                return

            ok, err = _corp_transfer_apply(int(uid), int(target_id), res_amount=0, mat_amount=int(amount))
            if not ok:
                bot.reply_to(message, err)
                return

            word = _ru_form(int(amount), "био-материал", "био-материала", "био-материалов")
            bot.reply_to(
                message,
                f"✅Успех. Игроку {_corp_actor_tag(int(target_id))} передано 💊 {_fmt_k(int(amount))} {word}.",
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
                    "Команда вступления <code>Био вступить</code> + название Корпорации",
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
                return
            corp = corp_by_id(my_cid)

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
                f"Подайте заявку на вступление, команда <code>Био вступить {h(nm)}</code>"
            )
            rm = kb_corp_info(int(corp["corp_id"]), viewer_id, False)

        bot.reply_to(message, text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=rm)
        return

# INLINE MODE
def _inline_strip_target_prefix(query: str) -> tuple[Optional[int], str, str]:
    raw = (query or "").strip()
    if not raw:
        return None, "", ""

    parts = raw.split(None, 1)
    tok = parts[0].strip()
    if tok.startswith("@"):
        tid = find_user_id_by_username(tok)
        tail = parts[1].strip() if len(parts) > 1 else ""
        return (int(tid), tok, tail) if tid is not None else (None, tok, tail)

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
            f"Подайте заявку на вступление, команда <code>Био вступить {h(nm)}</code>"
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

    if toks[0].isdigit() and len(toks) >= 2 and toks[1].startswith("@"):
        tid = find_user_id_by_username(toks[1])
        if tid is not None:
            return {"kind": "U", "target": int(tid), "count": max(1, int(toks[0]))}

    if toks[0].startswith("@"):
        tid = find_user_id_by_username(toks[0])
        if tid is not None:
            cnt = int(toks[1]) if len(toks) >= 2 and toks[1].isdigit() else 1
            return {"kind": "U", "target": int(tid), "count": max(1, cnt)}

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
            f"🦠 Подготовлено заражение цели {_corp_actor_tag(tid)}\n"
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

@bot.inline_handler(func=lambda q: True)
def inline_query_handler(inline_query):
    try:
        uid = int(inline_query.from_user.id)

        if is_bot_banned(uid):
            bot.answer_inline_query(inline_query.id, [], cache_time=0, is_personal=True)
            return

        upsert_user(inline_query.from_user)
        ensure_creator_is_support()
        ensure_lab_exists(uid)

        q_raw = (inline_query.query or "").strip()
        q = q_raw.lower()

        results = []

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
                        desc="",
                        text=text,
                        reply_markup=rm if int(inline_target_id) == int(uid) else None,
                        thumb_url=INLINE_THUMB_LAB_URL
                    ))

                if _inline_wants_balance(inline_tail):
                    text, rm = _render_inline_balance_for_viewer(uid, int(inline_target_id))
                    results.append(_inline_article(
                        article_id=f"bal_{uid}_{int(inline_target_id)}",
                        title="Баланс",
                        desc="",
                        text=text,
                        reply_markup=rm if int(inline_target_id) == int(uid) else None,
                        thumb_url=INLINE_THUMB_BAL_URL
                    ))

                if _inline_wants_corp(inline_tail):
                    text, rm = _render_inline_corp_for_viewer(uid, int(inline_target_id))
                    results.append(_inline_article(
                        article_id=f"corp_{uid}_{int(inline_target_id)}",
                        title="Досье корпорации",
                        desc="",
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
                    desc="",
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
                    desc="",
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
                    desc="",
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
                    desc="",
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
                    desc="",
                    text=_inline_infect_preview_text(inf_req),
                    reply_markup=kb_inline_infect_execute_mass(uid, mode, cnt),
                    thumb_url=INLINE_THUMB_INFECT_URL
                ))

        # калькулятор улучшения
        if not inline_target_token:
            mcalc = re.match(r"^([^\s]+)\s+(\d+)\s+(\d+)$", q)
            if mcalc:
                token = mcalc.group(1)
                n1 = int(mcalc.group(2))
                n2 = int(mcalc.group(3))
                code = _resolve_skill(token)
                if code and code in SKILLS:
                    cost = _calc_cost_range(SKILL_N1[code], n1, n2)
                    skill = SKILLS[code]
                    text = (
                        f"🧮 Калькулятор: {skill['emoji']} {h(skill['title_1'])} <b>{n1}</b> → <b>{n2}</b>\n"
                        f"Стоимость 🧬 <b>{_ru_dots(cost)}</b> ({_fmt_k(cost)})"
                    )
                    results.append(_inline_article(
                        article_id=f"calc_{uid}_{code}_{n1}_{n2}",
                        title="Калькулятор улучшения",
                        desc="",
                        text=text,
                        reply_markup=None,
                        thumb_url=INLINE_THUMB_CALC_URL
                    ))

        if results:
            bot.answer_inline_query(inline_query.id, results[:8], cache_time=0, is_personal=True)
            return

        bot.answer_inline_query(inline_query.id, [], cache_time=1, is_personal=True)
    except Exception as e:
        send_error_report("inline_query_handler", e)
        try:
            bot.answer_inline_query(inline_query.id, [], cache_time=2, is_personal=True)
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
            bot.reply_to(message, render_bot_ban_text(uid), disable_web_page_preview=True)
            return

        upsert_user(message.from_user)
        _handle_report_content_message(message)
    except Exception as e:
        send_error_report("on_report_media", e)

# MAIN ROUTER
@bot.message_handler(content_types=["text"])
def text_router(message):
    try:
        uid = int(message.from_user.id)

        if is_bot_banned(uid):
            if message.chat.type == "private":
                bot.reply_to(message, render_bot_ban_text(uid), disable_web_page_preview=True)
            return

        upsert_user(message.from_user)
        if getattr(message, "via_bot", None) is not None:
            return
        if message.chat.type in ("group", "supergroup"):
            remember_chat_member(message.chat.id, message.from_user)       
        ensure_creator_is_support()
        if message.chat.type == "private" and report_get_state(int(message.from_user.id))[0] == "await_content":
            if _handle_report_content_message(message):
                return

        parsed = parse_message_as_command(message.text)
        if not parsed:
            return

        # /owner
        if parsed.cmd == "owner":
            handle_owner_command(message, parsed)
            return
        
        # помощь
        if parsed.cmd == "help":
            handle_help_command(message)
            return

        # admin service
        if parsed.cmd in ("bot_ban", "bot_unban", "remake_lab"):
            handle_admin_service_commands(message, parsed)
            return

        # /settings
        if parsed.cmd == "settings":
            handle_settings_command(message)
            return
        
        # /report
        if parsed.cmd == "report":
            handle_report_command(message)
            return

        # приватные настройки
        if parsed.cmd in ("balance_hide", "balance_show", "lab_hide", "lab_show"):
            handle_privacy_toggle(message, parsed.cmd)
            return
        
        # уведомление
        if parsed.cmd in ("notify_on", "notify_off"):
            handle_notify_toggle(message, parsed.cmd)
            return

        # автоответчик
        if parsed.cmd in ("autoanswer_status", "autoanswer_on", "autoanswer_off"):
            handle_autoanswer_toggle(message, parsed.cmd)
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
        if parsed.cmd == "calc":
            handle_calc_command(message, parsed)
            return

        # использовать вакцину
        if parsed.cmd == "use_vaccine":
            uid = int(message.from_user.id)
            fever_until, fever_pat, vac_cnt = get_fever_and_vaccines(uid)
            now = now_ts()

            if fever_until <= now:
                bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости использовать вакцину.")
                return

            status, used = try_use_vaccine(uid, 1)
            if status == "OK":
                bot.reply_to(message, "💉 Вакцина излечила вас от горячки.\n🧾 Потрачена 1 единица вакцины")
            elif status == "FAIL":
                bot.reply_to(message, VACCINE_FAIL_TEXT, disable_web_page_preview=True, reply_markup=kb_vaccine_retry())
            elif status == "NO_VACCINE":
                price_txt = _fmt_bio_res(VACCINE_PRICE)
                kb = InlineKeyboardMarkup()
                kb.add(InlineKeyboardButton("💉 Купить вакцину", callback_data=CB_BUY_VACCINE))
                bot.reply_to(
                    message,
                    f"💉 Сейчас у вас нет ни одной вакцины. Для быстрого выздоровления вы можете купить вакцину: {price_txt}, "
                    f"команда <code>Био купить вакцину</code>",
                    disable_web_page_preview=True,
                    reply_markup=kb
                )
            else:
                bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости использовать вакцину.")
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
                kb.add(InlineKeyboardButton("💉 Использовать вакцину", callback_data=CB_USE_VACCINE))
                bot.reply_to(
                    message,
                    "💉 У вас нет необходимости покупать вакцину.  Для быстрого выздоровления используйте вакцину\n"
                    "команда <code>Био использовать вакцину</code>",
                    disable_web_page_preview=True,
                    reply_markup=kb
                )
                return

            status, spent_res, spent_mat = try_buy_vaccine(uid)
            if status == "NO_MONEY":
                bot.reply_to(message, "📝 У вас недостаточно средств.")
            elif status == "NO_FEVER":
                bot.reply_to(message, "📝 У вас нет горячки. Нет необходимости покупать вакцину.")
            elif status == "FAIL":
                bot.reply_to(message, VACCINE_FAIL_TEXT, disable_web_page_preview=True, reply_markup=kb_vaccine_retry())
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
            "corp_create", "corp_delete", "corp_open", "corp_close",
            "corp_reg", "corp_info", "corp_my", "corp_join", "corp_invite",
            "corp_req_accept", "corp_req_reject",
            "corp_deputy", "corp_kick", "corp_leave", "corp_transfer_owner",
            "corp_send_res", "corp_send_mat"
        ):
            handle_corp_commands(message, parsed)
            return
        
        # лаборатория
        if parsed.cmd in (
            "lab", "mylab", "labname", "pathogenname",
            "lab_delete", "restore_lab", "lab_delete_confirm_phrase"
        ):
            handle_lab_commands(message, parsed)
            return

    except Exception as e:
        send_error_report("text_router", e)

if __name__ == "__main__":
    init_db()
    init_deleted_db()
    ensure_creator_is_support()
    threading.Thread(target=_infection_daemon, daemon=True).start()
    threading.Thread(target=_pathogen_factory_daemon, daemon=True).start()
    threading.Thread(target=_vaccine_factory_daemon, daemon=True).start()
    threading.Thread(target=_housekeeping_daemon, daemon=True).start()
    print(f"@{BOT_USERNAME or 'unknown'} started...")
    while True:
        try:
            bot.infinity_polling(
                skip_pending=True,
                timeout=10,
                long_polling_timeout=20,
                allowed_updates=["message", "inline_query", "callback_query", "chat_member", "my_chat_member"]
            )
        except Exception as e:
            send_error_report("infinity_polling", e)
            time.sleep(5)