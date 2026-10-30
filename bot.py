"""
Telegram Dinner Menu Bot
------------------------
Keep a list of dishes sorted into categories (soup, stir-fry, fried/grilled, ...)
and get one random dinner suggestion from one chosen category every evening.

Buttons:
  🎲 ណែនាំម្ហូប   - today's suggestion (🔄 to change a dish, ✅ to accept)
  ➕ បន្ថែមម្ហូប   - pick a category, then type dish names (one per line or with commas)
  📋 បញ្ជីម្ហូប    - all dishes by category; open a category to delete dishes
  ⚙️ ការកំណត់     - suggestion time, which categories go into the suggestion

Commands:
  /start /help       - show buttons + how to use
  /suggest           - today's suggestion
  /add, /list        - same as the buttons
  /settings          - same as ⚙️
  /time 17:00        - when the daily suggestion is sent (/time off to stop)
  /addcat 🐟 ត្រី     - add a category
  /sample            - add some common Khmer dishes to start with

Groups:
  Every Telegram group (family) has its own dish list, categories and time.
  A private chat with the bot is a personal list.

Running / storage: same as the payment bot.
  - no WEBHOOK_URL -> polling (on your computer); WEBHOOK_URL / RENDER_EXTERNAL_URL -> webhook
  - DATABASE_URL set -> PostgreSQL, otherwise SQLite file DB_PATH (default menu.db)
  All tables start with "menu_", so this bot can share one database with the payment bot.
"""

import asyncio
import hashlib
import html
import logging
import os
import random
import re
import sqlite3
from collections import defaultdict
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

from telegram import (
    ForceReply,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyKeyboardMarkup,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ---------------- Settings (from environment variables) ----------------
TZ = ZoneInfo(os.getenv("BOT_TZ", "Asia/Phnom_Penh"))
DB_PATH = os.getenv("DB_PATH", "menu.db")
DATABASE_URL = os.getenv("DATABASE_URL")  # postgres://... -> use PostgreSQL
DEFAULT_TIME = os.getenv("SUGGEST_TIME", "17:00")  # daily suggestion time for new chats
REPEAT_DAYS = int(os.getenv("REPEAT_DAYS", "5"))  # try not to suggest a dish again within this many days
PENDING_MINUTES = 10  # how long the bot waits for dish names after picking a category
MAX_CATEGORIES = 15
MAX_DISH_LEN = 60

WEBHOOK_URL = (os.getenv("WEBHOOK_URL") or os.getenv("RENDER_EXTERNAL_URL") or "").rstrip("/")
PORT = int(os.getenv("PORT", "10000"))
CRON_SECRET = os.getenv("CRON_SECRET", "")  # protects the /cron/suggest address

# Categories every new chat starts with: (name, enabled for suggestions?)
DEFAULT_CATEGORIES = [
    ("🍲 សម្ល", True),
    ("🥘 ឆា", True),
    ("🍗 ចៀន/អាំង", True),
    ("🥗 ញាំ/បន្លែ", True),
    ("🍮 បង្អែម", True),
]
DESSERT_MARKER = "បង្អែម"
SAMPLE_DISHES = {
    "🍲 សម្ល": ["សម្លកកូរ", "សម្លម្ជូរគ្រឿង", "សម្លម្ជូរយួន", "ស្ងោរជ្រក់", "សម្លការី"],
    "🥘 ឆា": ["ឆាក្ដៅ", "ឆាត្រកួន", "ឆាសណ្ដែកកួរ", "ឆាខ្ញី", "ឆាផ្កាខាត់ណា"],
    "🍗 ចៀន/អាំង": ["ត្រីចៀន", "សាច់ជ្រូកអាំង", "មាន់អាំង", "ពងទាចៀន", "ប្រហុកចៀន"],
    "🥗 ញាំ/បន្លែ": ["ញាំស្វាយ", "ត្រប់ដុត", "ប្រហុកខ្ទិះ"],
    "🍮 បង្អែម": ["សង់ខ្យាល្ពៅ", "ចេកខ្ទិះ"],
}

# ---------------- Buttons ----------------
BTN_SUGGEST = "🎲 ណែនាំម្ហូប"
BTN_ADD = "➕ បន្ថែមម្ហូប"
BTN_LIST = "📋 បញ្ជីម្ហូប"
BTN_SETTINGS = "⚙️ ការកំណត់"

KEYBOARD = ReplyKeyboardMarkup(
    [[BTN_SUGGEST, BTN_ADD], [BTN_LIST, BTN_SETTINGS]],
    resize_keyboard=True,
    is_persistent=True,
)

# ---------------- Khmer text helpers ----------------
KHMER_DIGITS = str.maketrans("០១២៣៤៥៦៧៨៩", "0123456789")
TO_KHMER_DIGITS = str.maketrans("0123456789", "០១២៣៤៥៦៧៨៩")
KH_DAYS = ["ច័ន្ទ", "អង្គារ", "ពុធ", "ព្រហស្បតិ៍", "សុក្រ", "សៅរ៍", "អាទិត្យ"]
KH_MONTHS = ["មករា", "កុម្ភៈ", "មីនា", "មេសា", "ឧសភា", "មិថុនា",
             "កក្កដា", "សីហា", "កញ្ញា", "តុលា", "វិច្ឆិកា", "ធ្នូ"]

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
log = logging.getLogger("menu-bot")


def kh_num(n):
    return str(n).translate(TO_KHMER_DIGITS)


def kh_date(d):
    """date -> 'ថ្ងៃអង្គារ ២៧ តុលា'"""
    return f"ថ្ងៃ{KH_DAYS[d.weekday()]} {kh_num(d.day)} {KH_MONTHS[d.month - 1]}"


def today():
    return datetime.now(TZ).date()


def parse_hhmm(text):
    """'17:00' / '5:30' / '17' -> '17:00', or None."""
    m = re.match(r"^(\d{1,2})(?::(\d{2}))?$", text.translate(KHMER_DIGITS))
    if not m or int(m[1]) > 23 or int(m[2] or 0) > 59:
        return None
    return f"{int(m[1]):02d}:{int(m[2] or 0):02d}"


def split_dishes(text):
    """'សម្លកកូរ, ឆាក្ដៅ\\nត្រីចៀន' -> ['សម្លកកូរ', 'ឆាក្ដៅ', 'ត្រីចៀន'] (no duplicates)."""
    names = []
    for part in re.split(r"[\n,，、;]+", text):
        name = " ".join(part.split()).strip(" .។-•*")
        if name and len(name) <= MAX_DISH_LEN and name not in names:
            names.append(name)
    return names


def mention(user):
    """Clickable name; also makes a ForceReply reach this person in a group."""
    return f'<a href="tg://user?id={user.id}">{html.escape(user.first_name or str(user.id))}</a>'


# ---------------- Database (SQLite or PostgreSQL) ----------------
if DATABASE_URL:
    import psycopg
    from psycopg.rows import dict_row


def run(sql, args=(), fetch=None):
    """Run one SQL statement. Write SQL with '?' placeholders; fetch = None | 'one' | 'all'."""
    if DATABASE_URL:
        with psycopg.connect(DATABASE_URL, row_factory=dict_row) as conn:
            cur = conn.execute(sql.replace("?", "%s"), args)
            if fetch == "one":
                return cur.fetchone()
            if fetch == "all":
                return cur.fetchall()
            return None
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        with conn:
            cur = conn.execute(sql, args)
            if fetch == "one":
                return cur.fetchone()
            if fetch == "all":
                return cur.fetchall()
            return None
    finally:
        conn.close()


def init_db():
    auto_id = "BIGSERIAL PRIMARY KEY" if DATABASE_URL else "INTEGER PRIMARY KEY AUTOINCREMENT"
    run(
        f"CREATE TABLE IF NOT EXISTS menu_categories ("
        f" id {auto_id}, chat_id BIGINT NOT NULL, name TEXT NOT NULL,"
        f" daily INTEGER NOT NULL DEFAULT 1, UNIQUE (chat_id, name))"
    )
    run(
        f"CREATE TABLE IF NOT EXISTS menu_dishes ("
        f" id {auto_id}, chat_id BIGINT NOT NULL, category_id BIGINT NOT NULL,"
        f" name TEXT NOT NULL, added_by TEXT, created_at TEXT NOT NULL,"
        f" UNIQUE (chat_id, category_id, name))"
    )
    # one row per chat: suggestion time, and the day the last automatic suggestion went out
    run(
        "CREATE TABLE IF NOT EXISTS menu_settings ("
        " chat_id BIGINT PRIMARY KEY, suggest_at TEXT, last_sent TEXT)"
    )
    # which dish was suggested for each category on each day (used to avoid repeats)
    run(
        "CREATE TABLE IF NOT EXISTS menu_suggestions ("
        " chat_id BIGINT NOT NULL, day TEXT NOT NULL, category_id BIGINT NOT NULL,"
        " dish_id BIGINT NOT NULL, PRIMARY KEY (chat_id, day, category_id))"
    )
    log.info("Storage: %s", "PostgreSQL" if DATABASE_URL else f"SQLite file {DB_PATH}")


def get_settings(chat_id):
    return run("SELECT * FROM menu_settings WHERE chat_id=?", (chat_id,), fetch="one")


def save_settings(chat_id, **fields):
    cols = list(fields)
    assert set(cols) <= {"suggest_at", "last_sent"}
    run(
        f"INSERT INTO menu_settings (chat_id, {', '.join(cols)}) VALUES (?{', ?' * len(cols)}) "
        f"ON CONFLICT (chat_id) DO UPDATE SET " + ", ".join(f"{c}=excluded.{c}" for c in cols),
        (chat_id, *fields.values()),
    )


def ensure_chat(chat_id):
    """First time we see a chat: give it the default categories and the daily time."""
    if get_settings(chat_id) is not None:
        return
    for name, daily in DEFAULT_CATEGORIES:
        add_category(chat_id, name, daily)
    now = datetime.now(TZ)
    # time already passed today -> first suggestion tomorrow
    last = now.date().isoformat() if now.strftime("%H:%M") >= DEFAULT_TIME else None
    save_settings(chat_id, suggest_at=DEFAULT_TIME, last_sent=last)


def categories(chat_id):
    return run("SELECT * FROM menu_categories WHERE chat_id=? ORDER BY id", (chat_id,), fetch="all")


def category(chat_id, category_id):
    return run("SELECT * FROM menu_categories WHERE chat_id=? AND id=?",
               (chat_id, category_id), fetch="one")


def add_category(chat_id, name, daily=True):
    run("INSERT INTO menu_categories (chat_id, name, daily) VALUES (?, ?, ?) "
        "ON CONFLICT (chat_id, name) DO NOTHING", (chat_id, name, int(daily)))


def toggle_daily(chat_id, category_id):
    run("UPDATE menu_categories SET daily = 1 - daily WHERE chat_id=? AND id=?", (chat_id, category_id))


def delete_category(chat_id, category_id):
    run("DELETE FROM menu_dishes WHERE chat_id=? AND category_id=?", (chat_id, category_id))
    run("DELETE FROM menu_suggestions WHERE chat_id=? AND category_id=?", (chat_id, category_id))
    run("DELETE FROM menu_categories WHERE chat_id=? AND id=?", (chat_id, category_id))


def dishes(chat_id, category_id=None):
    sql, args = "SELECT * FROM menu_dishes WHERE chat_id=?", [chat_id]
    if category_id is not None:
        sql += " AND category_id=?"
        args.append(category_id)
    return run(sql + " ORDER BY name", args, fetch="all")


def add_dish(chat_id, category_id, name, added_by):
    """True if added, False if it was already in that category."""
    row = run(
        "INSERT INTO menu_dishes (chat_id, category_id, name, added_by, created_at) VALUES (?, ?, ?, ?, ?) "
        "ON CONFLICT (chat_id, category_id, name) DO NOTHING RETURNING id",
        (chat_id, category_id, name, added_by, datetime.now(TZ).isoformat(timespec="seconds")),
        fetch="one",
    )
    return row is not None


def delete_dish(chat_id, dish_id):
    return run("DELETE FROM menu_dishes WHERE chat_id=? AND id=? RETURNING name, category_id",
               (chat_id, dish_id), fetch="one")


def day_suggestion(chat_id, day):
    rows = run("SELECT category_id, dish_id FROM menu_suggestions WHERE chat_id=? AND day=?",
               (chat_id, day.isoformat()), fetch="all")
    return {r["category_id"]: r["dish_id"] for r in rows}


def save_suggestion(chat_id, day, category_id, dish_id):
    run("INSERT INTO menu_suggestions (chat_id, day, category_id, dish_id) VALUES (?, ?, ?, ?) "
        "ON CONFLICT (chat_id, day, category_id) DO UPDATE SET dish_id=excluded.dish_id",
        (chat_id, day.isoformat(), category_id, dish_id))


def save_daily_suggestions(chat_id, day, menu):
    run("DELETE FROM menu_suggestions WHERE chat_id=? AND day=?", (chat_id, day.isoformat()))
    for c, d in menu:
        save_suggestion(chat_id, day, c["id"], d["id"])


def recently_suggested(chat_id, day):
    """Dish ids suggested in the REPEAT_DAYS days before `day`."""
    rows = run("SELECT dish_id FROM menu_suggestions WHERE chat_id=? AND day>=? AND day<?",
               (chat_id, (day - timedelta(days=REPEAT_DAYS)).isoformat(), day.isoformat()), fetch="all")
    return {r["dish_id"] for r in rows}


def last_suggested_category(chat_id, day, category_ids):
    if not category_ids:
        return None
    placeholders = ", ".join("?" for _ in category_ids)
    row = run(
        "SELECT category_id FROM menu_suggestions WHERE chat_id=? AND day<? "
        f"AND category_id IN ({placeholders}) ORDER BY day DESC LIMIT 1",
        (chat_id, day.isoformat(), *category_ids),
        fetch="one",
    )
    return row["category_id"] if row else None


def dessert_day(chat_id, day):
    """Choose the same two pseudo-random dessert days for each chat every week."""
    week_start = day - timedelta(days=day.weekday())
    scores = [
        hashlib.sha256(f"{chat_id}:{week_start.isoformat()}:{weekday}".encode()).digest()
        for weekday in range(7)
    ]
    return day.weekday() in sorted(range(7), key=scores.__getitem__)[:2]


def chats_due(day):
    return run("SELECT chat_id, suggest_at FROM menu_settings WHERE suggest_at IS NOT NULL "
               "AND (last_sent IS NULL OR last_sent<>?)", (day.isoformat(),), fetch="all")


# ---------------- Suggestion ----------------
def pick(options, recent, avoid=None):
    """Random dish, preferring ones not suggested lately and not `avoid` (the one being changed)."""
    for pool in (
        [d for d in options if d["id"] not in recent and d["id"] != avoid],
        [d for d in options if d["id"] != avoid],
        options,
    ):
        if pool:
            return random.choice(pool)


def suggestion(chat_id, day, reroll=None):
    """Return one main dish and, on scheduled days, an optional dessert."""
    current = day_suggestion(chat_id, day)
    recent = recently_suggested(chat_id, day)
    by_cat = defaultdict(list)
    for d in dishes(chat_id):
        by_cat[d["category_id"]].append(d)

    enabled = [(c, by_cat[c["id"]]) for c in categories(chat_id)
               if c["daily"] and by_cat.get(c["id"])]
    main_options = [(c, options) for c, options in enabled
                    if DESSERT_MARKER not in c["name"]]
    dessert_options = [(c, options) for c, options in enabled
                       if DESSERT_MARKER in c["name"]]
    if not main_options:
        return []

    saved_main = next(
        ((c, d) for c, options in main_options for d in options
         if current.get(c["id"]) == d["id"]),
        None,
    )
    if saved_main is not None and reroll is None:
        main = saved_main
    else:
        main_ids = [c["id"] for c, _ in main_options]
        previous_category = last_suggested_category(chat_id, day, main_ids)
        avoid_category = saved_main[0]["id"] if saved_main else None
        preferred = [(c, options) for c, options in main_options
                     if c["id"] not in (previous_category, avoid_category)]
        if not preferred:
            preferred = [(c, options) for c, options in main_options
                         if c["id"] != avoid_category]
        if not preferred:
            preferred = main_options
        chosen_category, options = random.choice(preferred)
        avoid_dish = saved_main[1]["id"] if saved_main and saved_main[0]["id"] == chosen_category["id"] else None
        main = (chosen_category, pick(options, recent, avoid=avoid_dish))

    menu = [main]
    if dessert_options and dessert_day(chat_id, day):
        saved_dessert = next(
            ((c, d) for c, options in dessert_options for d in options
             if current.get(c["id"]) == d["id"]),
            None,
        )
        if saved_dessert is not None and reroll is None:
            menu.append(saved_dessert)
        else:
            dessert_category, options = random.choice(dessert_options)
            avoid_dish = saved_dessert[1]["id"] if saved_dessert and saved_dessert[0]["id"] == dessert_category["id"] else None
            menu.append((dessert_category, pick(options, recent, avoid=avoid_dish)))

    if {c["id"]: d["id"] for c, d in menu} != current:
        save_daily_suggestions(chat_id, day, menu)
    return menu


def suggestion_message(chat_id, day, reroll=None):
    """Text + buttons for the day's menu. Buttons are None when there's nothing to suggest."""
    menu = suggestion(chat_id, day, reroll)
    if not menu:
        return (
            "🍽 មិនទាន់មានម្ហូបសម្រាប់ណែនាំទេ។\n"
            f"ចុច {BTN_ADD} ដើម្បីបន្ថែមម្ហូប ឬវាយ /sample ដើម្បីបន្ថែមម្ហូបគំរូ។",
            None,
        )
    lines = [f"🍽 <b>ម្ហូបល្ងាចនេះ – {kh_date(day)}</b>", ""]
    for c, d in menu:
        lines.append(f"{html.escape(c['name'])}: <b>{html.escape(d['name'])}</b>")
    lines += ["", "🔄 ចុចដើម្បីចៃដន្យម្ហូបមួយទៀត ឬ ✅ បើយល់ព្រម"]
    rows = [[
        InlineKeyboardButton("🔄 ចៃដន្យម្ហូបមួយទៀត", callback_data="re:0"),
        InlineKeyboardButton("✅ យល់ព្រម", callback_data="ok:0"),
    ]]
    return "\n".join(lines), InlineKeyboardMarkup(rows)


# ---------------- Views (text + inline buttons) ----------------
def list_view(chat_id):
    cats = categories(chat_id)
    by_cat = defaultdict(list)
    for d in dishes(chat_id):
        by_cat[d["category_id"]].append(d["name"])
    total = sum(len(v) for v in by_cat.values())
    lines = [f"📋 <b>បញ្ជីម្ហូប</b> (សរុប {kh_num(total)} មុខ)", ""]
    for c in cats:
        names = by_cat.get(c["id"], [])
        lines.append(f"<b>{html.escape(c['name'])}</b> ({kh_num(len(names))})")
        lines.append(html.escape(", ".join(names)) if names else "<i>មិនទាន់មាន</i>")
        lines.append("")
    lines.append("ចុចប្រភេទខាងក្រោម ដើម្បីបន្ថែម ឬលុបម្ហូប")
    buttons = [InlineKeyboardButton(c["name"], callback_data=f"ls:{c['id']}") for c in cats]
    return "\n".join(lines), InlineKeyboardMarkup([buttons[i:i + 2] for i in range(0, len(buttons), 2)])


def category_view(chat_id, category_id):
    c = category(chat_id, category_id)
    if c is None:
        return list_view(chat_id)
    items = dishes(chat_id, category_id)
    text = f"<b>{html.escape(c['name'])}</b> – {kh_num(len(items))} មុខ"
    text += "\nចុច 🗑 ដើម្បីលុបម្ហូប" if items else "\nមិនទាន់មានម្ហូបទេ"
    rows = [[InlineKeyboardButton(f"🗑 {d['name']}", callback_data=f"rm:{d['id']}")] for d in items[:90]]
    rows.append([
        InlineKeyboardButton("➕ បន្ថែម", callback_data=f"add:{category_id}"),
        InlineKeyboardButton("⬅️ ត្រឡប់", callback_data="ls:0"),
    ])
    return text, InlineKeyboardMarkup(rows)


def add_view(chat_id):
    buttons = [InlineKeyboardButton(c["name"], callback_data=f"add:{c['id']}") for c in categories(chat_id)]
    if not buttons:
        return "មិនទាន់មានប្រភេទម្ហូបទេ។ បន្ថែមដោយ /addcat 🐟 ត្រី", None
    return ("➕ ជ្រើសរើសប្រភេទម្ហូប៖",
            InlineKeyboardMarkup([buttons[i:i + 2] for i in range(0, len(buttons), 2)]))


def settings_view(chat_id):
    s = get_settings(chat_id)
    at = s["suggest_at"] if s else None
    when = f"រាល់ថ្ងៃម៉ោង <b>{kh_num(at)}</b>" if at else "<b>បិទ</b>"
    text = (
        "⚙️ <b>ការកំណត់</b>\n\n"
        f"⏰ ណែនាំម្ហូប: {when}\n"
        "   /time 18:00 ដើម្បីប្តូរម៉ោង, /time off ដើម្បីបិទ\n\n"
        "📂 <b>ប្រភេទម្ហូប</b>\n"
        "   ✅ = អាចណែនាំ (ចុចដើម្បីប្តូរ); បង្អែមដែលមាន ✅ នឹងបន្ថែមចៃដន្យ ២ថ្ងៃ/សប្តាហ៍\n"
        "   /addcat 🐟 ត្រី ដើម្បីបន្ថែមប្រភេទថ្មី"
    )
    counts = defaultdict(int)
    for d in dishes(chat_id):
        counts[d["category_id"]] += 1
    rows = [
        [
            InlineKeyboardButton(f"{'✅' if c['daily'] else '⬜'} {c['name']} ({counts[c['id']]})",
                                 callback_data=f"tg:{c['id']}"),
            InlineKeyboardButton("🗑", callback_data=f"dc:{c['id']}"),
        ]
        for c in categories(chat_id)
    ]
    return text, InlineKeyboardMarkup(rows) if rows else None


# ---------------- Handlers ----------------
HELP_TEXT = (
    "👋 សួស្ដី! ខ្ញុំជួយកត់ត្រាបញ្ជីម្ហូប ហើយណែនាំម្ហូបរៀងរាល់ល្ងាច។\n\n"
    f"{BTN_ADD} – ជ្រើសប្រភេទ (សម្ល, ឆា, ចៀន/អាំង ...) រួចវាយឈ្មោះម្ហូប។\n"
    "   ច្រើនមុខក្នុងពេលតែមួយ៖ មួយបន្ទាត់មួយមុខ ឬដាក់សញ្ញាក្បៀស (,)\n"
    f"{BTN_SUGGEST} – មើលម្ហូបណែនាំថ្ងៃនេះ\n"
    f"{BTN_LIST} – មើល ឬលុបម្ហូប\n"
    f"{BTN_SETTINGS} – ម៉ោងណែនាំ និងប្រភេទម្ហូប\n\n"
    f"⏰ ខ្ញុំនឹងណែនាំម្ហូបរាល់ថ្ងៃម៉ោង {kh_num(DEFAULT_TIME)} (/time ដើម្បីប្តូរ)។\n"
    "🆕 វាយ /sample ដើម្បីបន្ថែមម្ហូបខ្មែរគំរូមួយចំនួន។"
)


def pending_key(chat_id):
    return f"adding:{chat_id}"


async def reply(update, text, markup=None):
    await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup or KEYBOARD)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_chat(update.effective_chat.id)
    await update.message.reply_text(HELP_TEXT, reply_markup=KEYBOARD)


async def suggest_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    ensure_chat(chat_id)
    await reply(update, *suggestion_message(chat_id, today()))


async def add_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_chat(update.effective_chat.id)
    await reply(update, *add_view(update.effective_chat.id))


async def list_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_chat(update.effective_chat.id)
    await reply(update, *list_view(update.effective_chat.id))


async def settings_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_chat(update.effective_chat.id)
    await reply(update, *settings_view(update.effective_chat.id))


async def time_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    ensure_chat(chat_id)
    arg = " ".join(context.args).strip().lower()
    if arg in ("off", "stop", "បិទ"):
        save_settings(chat_id, suggest_at=None)
        await reply(update, "🔕 បានបិទការណែនាំម្ហូបប្រចាំថ្ងៃ។ /time 17:00 ដើម្បីបើកវិញ។")
        return
    at = parse_hhmm(arg) if arg else None
    if at is None:
        await reply(update, "ប្រើ៖ /time 17:00  (ឬ /time off ដើម្បីបិទ)")
        return
    now = datetime.now(TZ)
    # time already passed today -> start tomorrow, don't send right away
    last = now.date().isoformat() if now.strftime("%H:%M") >= at else None
    save_settings(chat_id, suggest_at=at, last_sent=last)
    await reply(update, f"⏰ យល់ព្រម! ខ្ញុំនឹងណែនាំម្ហូបរាល់ថ្ងៃម៉ោង {kh_num(at)}។")


async def addcat_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    ensure_chat(chat_id)
    name = " ".join(" ".join(context.args).split())
    if not name or len(name) > 30 or name.startswith("/"):
        await reply(update, "ប្រើ៖ /addcat 🐟 ត្រី")
        return
    cats = categories(chat_id)
    if any(c["name"] == name for c in cats):
        await reply(update, f"មានប្រភេទ {html.escape(name)} រួចហើយ។")
        return
    if len(cats) >= MAX_CATEGORIES:
        await reply(update, f"មានប្រភេទបានច្រើនបំផុត {kh_num(MAX_CATEGORIES)}។ សូមលុបមួយសិនក្នុង {BTN_SETTINGS}។")
        return
    add_category(chat_id, name)
    await reply(update, f"✅ បានបន្ថែមប្រភេទ <b>{html.escape(name)}</b>។", add_view(chat_id)[1])


async def sample_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    ensure_chat(chat_id)
    by_name = {c["name"]: c["id"] for c in categories(chat_id)}
    added = 0
    for cat_name, names in SAMPLE_DISHES.items():
        if cat_name in by_name:
            added += sum(add_dish(chat_id, by_name[cat_name], n, "sample") for n in names)
    await reply(update, f"✅ បានបន្ថែមម្ហូបគំរូ {kh_num(added)} មុខ។ ចុច {BTN_SUGGEST} ដើម្បីសាកល្បង!")


async def save_dishes(update, context, category_id, text):
    msg = update.message
    chat_id = msg.chat_id
    c = category(chat_id, category_id)
    if c is None:
        await reply(update, "ប្រភេទនេះត្រូវបានលុបហើយ។")
        return
    names = split_dishes(text)
    if not names:
        await msg.reply_text(
            "សូមវាយឈ្មោះម្ហូប (ខ្លីជាង ៦០ តួអក្សរ)។",
            reply_markup=ForceReply(selective=True, input_field_placeholder="សម្លកកូរ"),
        )
        return
    context.user_data.pop(pending_key(chat_id), None)
    who = msg.from_user.full_name
    added = [n for n in names if add_dish(chat_id, category_id, n, who)]
    existing = [n for n in names if n not in added]
    lines = []
    if added:
        lines.append(f"✅ បានបន្ថែម {kh_num(len(added))} មុខក្នុង <b>{html.escape(c['name'])}</b>៖ "
                     + html.escape(", ".join(added)))
    if existing:
        lines.append("ℹ️ មានរួចហើយ៖ " + html.escape(", ".join(existing)))
    more = InlineKeyboardMarkup([[
        InlineKeyboardButton(f"➕ បន្ថែម{c['name']}ទៀត", callback_data=f"add:{category_id}"),
        InlineKeyboardButton("📂 ប្រភេទផ្សេង", callback_data="add:0"),
    ]])
    await reply(update, "\n".join(lines), more)


async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.message
    if not msg or not msg.text:
        return
    text = msg.text.strip()
    chat_id = msg.chat_id

    buttons = {BTN_SUGGEST: suggest_cmd, BTN_ADD: add_cmd, BTN_LIST: list_cmd, BTN_SETTINGS: settings_cmd}
    if text in buttons:
        context.user_data.pop(pending_key(chat_id), None)
        return await buttons[text](update, context)

    # --- dish names typed after picking a category ---
    pending = context.user_data.get(pending_key(chat_id))
    if pending:
        category_id, since = pending
        if datetime.now(TZ) - since > timedelta(minutes=PENDING_MINUTES):
            context.user_data.pop(pending_key(chat_id), None)
            return  # too old, treat as normal chat
        return await save_dishes(update, context, category_id, text)

    # anything else = normal chat, ignore


async def edit(query, text, markup=None):
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    except BadRequest as e:
        if "not modified" not in str(e).lower():  # same text (e.g. only one dish) is fine
            raise


async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    action, _, arg = query.data.partition(":")
    arg = int(arg)
    chat_id = query.message.chat.id
    ensure_chat(chat_id)

    if action == "add":  # pick a category to add to (0 = show the categories)
        if arg == 0:
            await query.answer()
            return await edit(query, *add_view(chat_id))
        c = category(chat_id, arg)
        if c is None:
            return await query.answer("ប្រភេទនេះត្រូវបានលុបហើយ។", show_alert=True)
        await query.answer()
        context.user_data[pending_key(chat_id)] = (arg, datetime.now(TZ))
        await query.message.reply_text(
            f"✍️ {mention(query.from_user)} វាយឈ្មោះម្ហូបសម្រាប់ <b>{html.escape(c['name'])}</b>\n"
            "ច្រើនមុខ៖ មួយបន្ទាត់មួយមុខ ឬដាក់សញ្ញាក្បៀស (,)",
            parse_mode=ParseMode.HTML,
            reply_markup=ForceReply(selective=True, input_field_placeholder="សម្លកកូរ, ឆាក្ដៅ"),
        )

    elif action == "ls":  # dish list (0) or one category
        await query.answer()
        await edit(query, *(list_view(chat_id) if arg == 0 else category_view(chat_id, arg)))

    elif action == "rm":  # delete a dish
        row = delete_dish(chat_id, arg)
        if row is None:
            await query.answer("ម្ហូបនេះត្រូវបានលុបរួចហើយ។")
            return await edit(query, *list_view(chat_id))
        await query.answer(f"🗑 បានលុប {row['name']}")
        await edit(query, *category_view(chat_id, row["category_id"]))

    elif action == "re":  # choose a different random dish for today's suggestion
        await query.answer("🔄")
        await edit(query, *suggestion_message(chat_id, today(), reroll="all"))

    elif action == "ok":  # menu accepted: keep the text, remove the buttons
        await query.answer("😋")
        menu = suggestion(chat_id, today())
        lines = [f"🍽 <b>ម្ហូបល្ងាចនេះ – {kh_date(today())}</b>", ""]
        lines += [f"{html.escape(c['name'])}: <b>{html.escape(d['name'])}</b>" for c, d in menu]
        lines += ["", f"✅ {mention(query.from_user)} យល់ព្រមហើយ។ ធ្វើម្ហូបឆ្ងាញ់ៗណា! 😋"]
        await edit(query, "\n".join(lines))

    elif action == "tg":  # category in / out of the daily suggestion
        toggle_daily(chat_id, arg)
        await query.answer()
        await edit(query, *settings_view(chat_id))

    elif action == "dc":  # delete a category: ask first
        c = category(chat_id, arg)
        if c is None:
            await query.answer()
            return await edit(query, *settings_view(chat_id))
        await query.answer()
        n = len(dishes(chat_id, arg))
        await edit(
            query,
            f"🗑 លុបប្រភេទ <b>{html.escape(c['name'])}</b> និងម្ហូប {kh_num(n)} មុខរបស់វា?",
            InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ លុប", callback_data=f"dy:{arg}"),
                InlineKeyboardButton("✖️ បោះបង់", callback_data="st:0"),
            ]]),
        )

    elif action == "dy":  # delete a category: confirmed
        delete_category(chat_id, arg)
        await query.answer("🗑 បានលុប")
        await edit(query, *settings_view(chat_id))

    elif action == "st":  # back to settings
        await query.answer()
        await edit(query, *settings_view(chat_id))


async def on_migrate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """A group that becomes a 'supergroup' gets a new id: move its menu over."""
    msg = update.message
    if msg and msg.migrate_to_chat_id:
        for table in ("menu_categories", "menu_dishes", "menu_settings", "menu_suggestions"):
            run(f"UPDATE {table} SET chat_id=? WHERE chat_id=?", (msg.migrate_to_chat_id, msg.chat_id))
        log.info("Group %s upgraded to %s: menu moved", msg.chat_id, msg.migrate_to_chat_id)


# ---------------- Daily suggestion ----------------
_suggestion_lock = asyncio.Lock()


async def send_due_suggestions(bot, now=None):
    """Send today's menu to every chat whose time has come. Each chat gets it once a day."""
    async with _suggestion_lock:
        now = now or datetime.now(TZ)
        day = now.date()
        sent = 0
        for r in chats_due(day):
            if now.strftime("%H:%M") < r["suggest_at"]:
                continue
            chat_id = r["chat_id"]
            text, markup = suggestion_message(chat_id, day)
            if markup is None:
                save_settings(chat_id, last_sent=day.isoformat())
                continue  # no dishes yet, don't bother the chat
            try:
                await bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=markup)
            except Exception as e:  # bot removed from group, etc.
                log.warning("Could not send suggestion to %s: %s", chat_id, e)
                continue
            sent += 1
            save_settings(chat_id, last_sent=day.isoformat())
        return sent


async def suggestion_job(context: ContextTypes.DEFAULT_TYPE):
    sent = await send_due_suggestions(context.bot)
    if sent:
        log.info("Sent %d suggestion(s)", sent)


# ---------------- Building the bot ----------------
def build_application(token, request=None):
    builder = Application.builder().token(token)
    if request is not None:  # used by tests
        builder = builder.request(request).get_updates_request(request)
    else:
        builder = (
            builder
            # slow / unstable internet: wait longer before giving up
            .connect_timeout(30).read_timeout(30).write_timeout(30).pool_timeout(30)
            .get_updates_connect_timeout(30).get_updates_read_timeout(60)
        )
        proxy = os.getenv("PROXY")  # e.g. http://127.0.0.1:7890 or socks5://127.0.0.1:1080
        if proxy:
            builder = builder.proxy(proxy).get_updates_proxy(proxy)
            log.info("Using proxy %s", proxy)
    app = builder.build()

    new_msg = filters.UpdateType.MESSAGE  # ignore edited messages
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, on_migrate))
    app.add_handler(CommandHandler(["start", "help"], start, filters=new_msg))
    app.add_handler(CommandHandler("suggest", suggest_cmd, filters=new_msg))
    app.add_handler(CommandHandler("add", add_cmd, filters=new_msg))
    app.add_handler(CommandHandler("list", list_cmd, filters=new_msg))
    app.add_handler(CommandHandler("settings", settings_cmd, filters=new_msg))
    app.add_handler(CommandHandler("time", time_cmd, filters=new_msg))
    app.add_handler(CommandHandler("addcat", addcat_cmd, filters=new_msg))
    app.add_handler(CommandHandler("sample", sample_cmd, filters=new_msg))
    app.add_handler(CallbackQueryHandler(on_button, pattern=r"^[a-z]{2,3}:\d+$"))
    app.add_handler(MessageHandler(new_msg & filters.TEXT & ~filters.COMMAND, on_message))

    # Look every 5 minutes for chats whose suggestion time has come.
    app.job_queue.run_repeating(suggestion_job, interval=300, first=20)
    return app


def webhook_secret(token):
    """Secret Telegram sends with every update, so strangers can't post fake ones."""
    return hashlib.sha256(("webhook:" + token).encode()).hexdigest()[:48]


def build_web(app, token):
    """Small web server: Telegram posts messages to /telegram; cron-job.org calls the others."""
    from starlette.applications import Starlette
    from starlette.responses import PlainTextResponse, Response
    from starlette.routing import Route

    secret = webhook_secret(token)

    async def telegram(request):
        if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != secret:
            return Response(status_code=403)
        await app.update_queue.put(Update.de_json(await request.json(), app.bot))
        return Response()

    async def health(request):
        return PlainTextResponse("Menu bot is running")

    async def cron(request):
        if not CRON_SECRET or request.query_params.get("key") != CRON_SECRET:
            return PlainTextResponse("Forbidden", status_code=403)
        return PlainTextResponse(f"sent {await send_due_suggestions(app.bot)}")

    return Starlette(routes=[
        Route("/", health, methods=["GET", "HEAD"]),
        Route("/telegram", telegram, methods=["POST"]),
        Route("/cron/suggest", cron, methods=["GET", "POST"]),
    ])


async def run_webhook(app, token, base_url, port):
    import uvicorn
    server = uvicorn.Server(uvicorn.Config(build_web(app, token), host="0.0.0.0", port=port, log_level="warning"))
    async with app:  # initialize / shutdown
        await app.bot.set_webhook(
            url=f"{base_url}/telegram",
            allowed_updates=Update.ALL_TYPES,
            secret_token=webhook_secret(token),
        )
        await app.start()
        log.info("Bot started (online mode): %s/telegram", base_url)
        await server.serve()  # runs until the host stops the app
        await app.stop()


# ---------------- Main ----------------
def main():
    token = os.getenv("BOT_TOKEN")
    if not token:
        raise SystemExit("Please set the BOT_TOKEN environment variable.")
    init_db()
    app = build_application(token)

    if WEBHOOK_URL:
        asyncio.run(run_webhook(app, token, WEBHOOK_URL, PORT))
    else:
        log.info("Bot started (computer mode).")
        # bootstrap_retries=-1: keep retrying at startup instead of crashing
        app.run_polling(allowed_updates=Update.ALL_TYPES, bootstrap_retries=-1, drop_pending_updates=False)


if __name__ == "__main__":
    main()
