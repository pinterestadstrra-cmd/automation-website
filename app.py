#!/usr/bin/env python3
"""
Automation Website - app.py
================================
Blogger auto-posting + Bluesky marketing dashboard and worker.

WHAT IT DOES
------------
1. MOST IMPORTANT: checks what is TRENDING on Bluesky FIRST, then writes
   news based on those trending topics (not the other way round).
2. Verifies every story with >= 2 independent sources before publishing.
3. Writes articles with a hook + SEO (Gemini), images with NO logo/text.
4. STRICT RULE: NO photo = NO post. A topic with no suitable photo is
   dropped entirely (never text-only, never a placeholder).
5. Publishes to Blogger (daily cap is a manual card setting; too many
   posts risks a Blogger suspension, so posts are spaced out).
6. Posts to Bluesky every 30 minutes (GitHub Actions cron). The SAME post
   never goes to all Bluesky accounts - each account gets a different /
   rotated post. Dedup via data/state.json (same news never reposted).
7. Replies to comments on the account's OWN posts (all of them), and -
   with strict safety limits - to fresh comments on high-engagement posts.
   Every reply is unique English text (never copy-paste duplicates).
8. Dashboard (flat UI, white / sky-blue / red / teal) with fully MANUAL
   cards: link to market, account, post/reply count, interval (minutes),
   daily schedule (how many + at what times), Run / Pause / Delete,
   live status. Everything is saved in the database, so a refresh loses
   nothing and the site keeps running while the user is offline
   (GitHub Actions does the work on schedule).

SECRETS (never in the repo - GitHub Secrets / environment only)
---------------------------------------------------------------
  GEMINI_API_KEYS        comma-separated Gemini keys (separate Google projects)
  GROQ_API_KEYS          comma-separated Groq keys (separate Groq accounts)
  BLOGGER_CLIENT_ID      Google OAuth client id (Blogger API enabled)
  BLOGGER_CLIENT_SECRET  Google OAuth client secret
  BLOGGER_REFRESH_TOKEN  Blogger OAuth refresh token (offline access)
  BLOG_ID                Blogger blog id
  BLUESKY_ACCOUNTS       JSON list [{"handle": "...", "app_password": "..."}]
  PEXELS_API_KEY         (optional) free Pexels key for photos
  PIXABAY_API_KEY        (optional) free Pixabay key for photos
  ADMIN_PASSWORD         dashboard password (admin panel)
  SECRET_KEY             Flask session secret (any random string)

RUN
---
  Web dashboard :  python app.py            (then open http://localhost:5000)
  One worker run:  python app.py --worker   (what GitHub Actions runs)
  Docker        :  docker build -t automation-website . && docker run -p 5000:5000 --env-file .env automation-website
"""

import os
import sys
import json
import time
import random
import re
import hashlib
import sqlite3
import threading
import html as html_lib
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from urllib.parse import quote_plus, urlparse

import requests
from flask import Flask, request, jsonify, session, send_from_directory, g

# ---------------------------------------------------------------- optional deps
try:
    from googleapiclient.discovery import build as google_build
    from google.oauth2.credentials import Credentials as GoogleCredentials
    GOOGLE_AVAILABLE = True
except Exception:  # pragma: no cover - library not installed
    google_build = None
    GoogleCredentials = None
    GOOGLE_AVAILABLE = False

try:
    from atproto import Client as AtprotoClient
    ATPROTO_AVAILABLE = True
except Exception:  # pragma: no cover - library not installed
    AtprotoClient = None
    ATPROTO_AVAILABLE = False

# ---------------------------------------------------------------- config
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
IMAGES_DIR = os.path.join(DATA_DIR, "images")
DB_PATH = os.path.join(DATA_DIR, "app.db")
STATE_PATH = os.path.join(DATA_DIR, "state.json")
LOGS_PATH = os.path.join(DATA_DIR, "logs.json")
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
DASHBOARD_PATH = os.path.join(DATA_DIR, "dashboard.json")
os.makedirs(IMAGES_DIR, exist_ok=True)

SECRET_KEY = os.environ.get("SECRET_KEY", "change-this-secret-key")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "changeme123")

GEMINI_KEYS = [k.strip() for k in os.environ.get("GEMINI_API_KEYS", "").split(",") if k.strip()]
GROQ_KEYS = [k.strip() for k in os.environ.get("GROQ_API_KEYS", "").split(",") if k.strip()]

BLOGGER_CLIENT_ID = os.environ.get("BLOGGER_CLIENT_ID", "")
BLOGGER_CLIENT_SECRET = os.environ.get("BLOGGER_CLIENT_SECRET", "")
BLOGGER_REFRESH_TOKEN = os.environ.get("BLOGGER_REFRESH_TOKEN", "")
BLOG_ID = os.environ.get("BLOG_ID", "")

PEXELS_API_KEY = os.environ.get("PEXELS_API_KEY", "")
PIXABAY_API_KEY = os.environ.get("PIXABAY_API_KEY", "")

# Bluesky accounts can come from the env secret (GitHub Actions) or from
# the dashboard database (cards). Env wins for the worker; the dashboard
# lets the user add accounts in a card and stores them in the DB.
def _load_env_bluesky_accounts():
    raw = os.environ.get("BLUESKY_ACCOUNTS", "").strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [a for a in data if a.get("handle") and a.get("app_password")]
    except Exception:
        pass
    return []

ENV_BLUESKY_ACCOUNTS = _load_env_bluesky_accounts()

# Gemini models to try, in order (free-tier friendly first).
GEMINI_MODELS = ["gemini-2.5-flash-lite", "gemini-2.0-flash", "gemini-2.5-flash"]
# Groq models to try, in order (free tier, confirmed model ids).
GROQ_MODELS = ["openai/gpt-oss-120b", "openai/gpt-oss-20b"]

# Limits: 0 = UNLIMITED (no cap). The user chose unlimited.
# WARNING: unlimited posting risks a Blogger suspension and Bluesky
# spam flags / account bans. The 429 auto-pause is still active.
DEFAULT_BLOGGER_DAILY_LIMIT = 0        # 0 = unlimited posts per day
DEFAULT_BSKY_REPLY_PER_RUN = 0        # 0 = unlimited replies per run
DEFAULT_BSKY_REPLY_DAILY_CAP = 0      # 0 = unlimited replies per day
DEFAULT_REPLY_GAP_SECONDS = 0         # 0 = no gap between replies
DEFAULT_BSKY_POSTS_PER_RUN = 1        # max 1 Bluesky post per run

UTC = timezone.utc


def now_utc():
    return datetime.now(UTC)


def now_iso():
    return now_utc().isoformat()


def today_str():
    return now_utc().strftime("%Y-%m-%d")


# ---------------------------------------------------------------- flask app
app = Flask(__name__)
app.secret_key = SECRET_KEY
app.config["JSON_SORT_KEYS"] = False

# ---------------------------------------------------------------- database
def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
    return g.db


@app.teardown_appcontext
def close_db(_exc=None):
    db = g.pop("db", None)
    if db is not None:
        db.close()


def db_connect():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    conn = db_connect()
    cur = conn.cursor()
    cur.executescript("""
    CREATE TABLE IF NOT EXISTS accounts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        handle TEXT UNIQUE NOT NULL,
        app_password TEXT NOT NULL,
        display_name TEXT DEFAULT '',
        active INTEGER DEFAULT 1,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS cards (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        type TEXT NOT NULL,
        link TEXT DEFAULT '',
        account_handle TEXT DEFAULT '',
        count INTEGER DEFAULT 1,
        interval_minutes INTEGER DEFAULT 30,
        schedule_times TEXT DEFAULT '[]',
        text TEXT DEFAULT '',
        status TEXT DEFAULT 'active',
        done_count INTEGER DEFAULT 0,
        last_run TEXT DEFAULT '',
        next_run TEXT DEFAULT '',
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS posts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT NOT NULL,
        url TEXT DEFAULT '',
        topic TEXT DEFAULT '',
        source TEXT DEFAULT '',
        image_url TEXT DEFAULT '',
        status TEXT DEFAULT 'published',
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS replies (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        post_uri TEXT DEFAULT '',
        comment_uri TEXT DEFAULT '',
        reply_text TEXT DEFAULT '',
        account_handle TEXT DEFAULT '',
        status TEXT DEFAULT 'sent',
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS logs (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        level TEXT DEFAULT 'info',
        message TEXT NOT NULL,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS settings (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL
    );
    """)
    defaults = {
        "blogger_daily_limit": str(DEFAULT_BLOGGER_DAILY_LIMIT),
        "bsky_reply_per_run": str(DEFAULT_BSKY_REPLY_PER_RUN),
        "bsky_reply_daily_cap": str(DEFAULT_BSKY_REPLY_DAILY_CAP),
        "reply_gap_seconds": str(DEFAULT_REPLY_GAP_SECONDS),
        "bsky_posts_per_run": str(DEFAULT_BSKY_POSTS_PER_RUN),
    }
    for k, v in defaults.items():
        cur.execute("INSERT OR IGNORE INTO settings(key, value) VALUES(?, ?)", (k, v))
    conn.commit()
    conn.close()


_FILE_CONFIG = None


def file_config():
    """Settings from data/config.json (the GitHub-only control panel).
    Edit this file in the repo to change limits - no server needed.
    Returns {} when the file is missing."""
    global _FILE_CONFIG
    if _FILE_CONFIG is None:
        _FILE_CONFIG = {}
        if os.path.exists(CONFIG_PATH):
            try:
                with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    _FILE_CONFIG = data
            except Exception as e:
                print(f"config.json load failed: {e}", flush=True)
    return _FILE_CONFIG


def get_setting(key, default=""):
    # data/config.json wins over the database (GitHub-only control).
    cfg = file_config()
    if key in cfg:
        return str(cfg[key])
    conn = db_connect()
    try:
        row = conn.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
        return row["value"] if row else default
    finally:
        conn.close()


def set_setting(key, value):
    conn = db_connect()
    try:
        conn.execute("INSERT INTO settings(key, value) VALUES(?, ?) "
                     "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                     (key, str(value)))
        conn.commit()
    finally:
        conn.close()


def log(level, message):
    """Write a log row (dashboard activity log) and print it."""
    msg = str(message)[:1000]
    try:
        conn = db_connect()
        try:
            conn.execute("INSERT INTO logs(level, message, created_at) VALUES(?, ?, ?)",
                         (level, msg, now_iso()))
            conn.execute("DELETE FROM logs WHERE id NOT IN "
                         "(SELECT id FROM logs ORDER BY id DESC LIMIT 500)")
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass
    print(f"[{now_iso()}] {level.upper()}: {msg}", flush=True)


# ---------------------------------------------------------------- json state file
# GitHub Actions runners are fresh VMs, so the SQLite DB does not survive
# between runs. data/state.json IS committed back to the repo, so dedup
# (posted news, replied comments) survives across runs.
def load_state():
    if os.path.exists(STATE_PATH):
        try:
            with open(STATE_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                return data
        except Exception:
            pass
    return {"posted_urls": [], "posted_topics": [], "replied_comments": [],
            "last_run": "", "runs": 0}


def save_state(state):
    try:
        state["posted_urls"] = state.get("posted_urls", [])[-500:]
        state["posted_topics"] = state.get("posted_topics", [])[-500:]
        state["replied_comments"] = state.get("replied_comments", [])[-2000:]
        with open(STATE_PATH, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"state save failed: {e}", flush=True)


def append_logs_json():
    """Mirror the latest logs into data/logs.json for the repo commit."""
    try:
        conn = db_connect()
        try:
            rows = conn.execute("SELECT level, message, created_at FROM logs "
                                "ORDER BY id DESC LIMIT 100").fetchall()
        finally:
            conn.close()
        with open(LOGS_PATH, "w", encoding="utf-8") as f:
            json.dump([dict(r) for r in rows], f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def write_dashboard_json(state):
    """Write data/dashboard.json - the status file the STATIC Pages
    dashboard reads. Contains NO secrets (only public status: posts,
    logs, trending topics, settings). The workflow commits it back so
    GitHub Pages always shows the latest run."""
    try:
        conn = db_connect()
        try:
            posts = [dict(r) for r in conn.execute(
                "SELECT title, url, topic, source, image_url, created_at FROM posts "
                "ORDER BY id DESC LIMIT 10").fetchall()]
            logs = [dict(r) for r in conn.execute(
                "SELECT level, message, created_at FROM logs ORDER BY id DESC LIMIT 50"
                ).fetchall()]
            total_posts = conn.execute("SELECT COUNT(*) c FROM posts").fetchone()["c"]
            total_replies = conn.execute("SELECT COUNT(*) c FROM replies").fetchone()["c"]
        finally:
            conn.close()
        try:
            trending = get_bluesky_trending(limit=10)
        except Exception:
            trending = []
        data = {
            "generated_at": now_iso(),
            "last_run": state.get("last_run", ""),
            "runs": state.get("runs", 0),
            "stats": {
                "blogger_today": blogger_posts_today(),
                "replies_today": replies_today(),
                "total_posts": total_posts,
                "total_replies": total_replies,
                "accounts": len(list_accounts()),
            },
            "settings": {k: get_setting(k, "") for k in
                         ("blogger_daily_limit", "bsky_reply_per_run",
                          "bsky_reply_daily_cap", "reply_gap_seconds",
                          "bsky_posts_per_run", "paused", "force_topic")},
            "account_handles": [a["handle"] for a in list_accounts()],
            "trending": trending,
            "recent_posts": posts,
            "logs": logs,
        }
        with open(DASHBOARD_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"dashboard.json write failed: {e}", flush=True)


def slugify(text):
    text = re.sub(r"[^a-zA-Z0-9]+", "-", (text or "").strip().lower()).strip("-")
    return text[:80] or "post"

# ---------------------------------------------------------------- AI clients
# Gemini writes, Groq handles the rest. Keys rotate (failover) so one dead
# key never stops the run. Gemini quota is per Google project, Groq quota
# is per Groq account - so keys MUST come from different projects/accounts
# for the quota to multiply.

def _gemini_call(key, model, prompt, max_tokens):
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/{model}"
           f":generateContent?key={key}")
    body = {"contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": {"maxOutputTokens": max_tokens,
                                 "temperature": 0.7}}
    r = requests.post(url, json=body, timeout=60)
    if r.status_code != 200:
        return None, r.status_code
    try:
        text = r.json()["candidates"][0]["content"]["parts"][0]["text"]
        return (text or "").strip(), 200
    except Exception:
        return None, 200


def gemini_text(prompt, max_tokens=1500):
    """Write with Gemini. Returns text or '' (never raises)."""
    if not GEMINI_KEYS:
        log("warning", "gemini_text: no GEMINI_API_KEYS configured")
        return ""
    keys = GEMINI_KEYS[:]
    random.shuffle(keys)
    for model in GEMINI_MODELS:
        for key in keys:
            try:
                text, code = _gemini_call(key, model, prompt, max_tokens)
                if text:
                    return text
                if code == 429:
                    time.sleep(2)
            except Exception as e:
                log("warning", f"gemini {model} error: {e}")
    log("warning", "gemini_text: all keys/models failed")
    return ""


def _groq_call(key, model, prompt, max_tokens):
    url = "https://api.groq.com/openai/v1/chat/completions"
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    body = {"model": model,
            "messages": [{"role": "user", "content": prompt}],
            "max_tokens": max_tokens, "temperature": 0.7}
    r = requests.post(url, json=body, headers=headers, timeout=60)
    if r.status_code != 200:
        return None, r.status_code
    try:
        text = r.json()["choices"][0]["message"]["content"]
        return (text or "").strip(), 200
    except Exception:
        return None, 200


def groq_text(prompt, max_tokens=800):
    """Fast replies / small jobs with Groq. Returns text or ''."""
    if not GROQ_KEYS:
        log("warning", "groq_text: no GROQ_API_KEYS configured")
        return ""
    keys = GROQ_KEYS[:]
    random.shuffle(keys)
    for model in GROQ_MODELS:
        for key in keys:
            try:
                text, code = _groq_call(key, model, prompt, max_tokens)
                if text:
                    return text
                if code == 429:
                    time.sleep(2)
            except Exception as e:
                log("warning", f"groq {model} error: {e}")
    log("warning", "groq_text: all keys/models failed")
    return ""


def ai_write(prompt, max_tokens=1500):
    """Primary writer: Gemini, Groq as fallback."""
    text = gemini_text(prompt, max_tokens=max_tokens)
    if text:
        return text
    return groq_text(prompt, max_tokens=max_tokens)


# ---------------------------------------------------------------- photos
# STRICT RULE: no photo = no post. Real stock photos first (clean, no
# logo/text). Pollinations (AI image, nologo) is only the last fallback.
# A topic is dropped ONLY when no image can be obtained from any source.
BAD_PHOTO_WORDS = ("logo", "watermark", "banner", "text overlay", "advert")


def _photo_ok(meta):
    title = (meta.get("alt") or meta.get("title") or "").lower()
    return not any(w in title for w in BAD_PHOTO_WORDS)


def _pexels_photo(topic):
    if not PEXELS_API_KEY:
        return None
    try:
        r = requests.get("https://api.pexels.com/v1/search",
                         params={"query": topic, "per_page": 5, "orientation": "landscape"},
                         headers={"Authorization": PEXELS_API_KEY}, timeout=20)
        if r.status_code != 200:
            return None
        for p in r.json().get("photos", []):
            src = p.get("src", {})
            url = src.get("large2x") or src.get("large") or src.get("original")
            meta = {"alt": p.get("alt") or "", "title": ""}
            if url and _photo_ok(meta):
                return {"url": url, "source": "pexels", "alt": meta["alt"]}
    except Exception as e:
        log("warning", f"pexels error: {e}")
    return None


def _pixabay_photo(topic):
    if not PIXABAY_API_KEY:
        return None
    try:
        r = requests.get("https://pixabay.com/api/",
                         params={"key": PIXABAY_API_KEY, "q": topic,
                                 "image_type": "photo", "per_page": 5,
                                 "orientation": "horizontal", "safesearch": "true"},
                         timeout=20)
        if r.status_code != 200:
            return None
        for h in r.json().get("hits", []):
            url = h.get("largeImageURL") or h.get("webformatURL")
            meta = {"alt": h.get("tags") or "", "title": ""}
            if url and _photo_ok(meta):
                return {"url": url, "source": "pixabay", "alt": meta["alt"]}
    except Exception as e:
        log("warning", f"pixabay error: {e}")
    return None


def _openverse_photo(topic):
    try:
        r = requests.get("https://api.openverse.org/v1/images/",
                         params={"q": topic, "page_size": 5, "license_type": "commercial"},
                         timeout=20)
        if r.status_code != 200:
            return None
        for item in r.json().get("results", []):
            url = item.get("url") or item.get("foreign_landing_url")
            meta = {"alt": item.get("title") or "", "title": item.get("title") or ""}
            if url and _photo_ok(meta):
                return {"url": url, "source": "openverse", "alt": meta["alt"]}
    except Exception as e:
        log("warning", f"openverse error: {e}")
    return None


def _pollinations_photo(topic):
    """AI-generated image, no logo. Last fallback only."""
    try:
        prompt = quote_plus(f"{topic}, dramatic news photo, daytime, photorealistic, 16:9")
        url = (f"https://image.pollinations.ai/prompt/{prompt}"
               f"?width=1280&height=720&nologo=true&model=flux")
        r = requests.get(url, timeout=90)
        if r.status_code == 200 and len(r.content) > 20000:
            fname = f"pollinations-{slugify(topic)}-{int(time.time())}.jpg"
            path = os.path.join(IMAGES_DIR, fname)
            with open(path, "wb") as f:
                f.write(r.content)
            return {"url": f"/images/{fname}", "source": "pollinations",
                    "alt": topic, "local_path": path}
    except Exception as e:
        log("warning", f"pollinations error: {e}")
    return None


def download_image(url, topic):
    try:
        r = requests.get(url, timeout=30,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200 or len(r.content) < 10000:
            return None
        ext = ".jpg"
        if "png" in (r.headers.get("Content-Type") or ""):
            ext = ".png"
        fname = f"{slugify(topic)}-{int(time.time())}{ext}"
        path = os.path.join(IMAGES_DIR, fname)
        with open(path, "wb") as f:
            f.write(r.content)
        return path
    except Exception as e:
        log("warning", f"download_image error: {e}")
        return None


def fetch_photo(topic):
    """Find a clean photo for a topic. Returns dict or None (strict)."""
    for fn in (_pexels_photo, _pixabay_photo, _openverse_photo):
        try:
            found = fn(topic)
        except Exception:
            found = None
        if found:
            local = download_image(found["url"], topic)
            if local:
                found["local_path"] = local
                log("info", f"photo: {found['source']} for '{topic}'")
                return found
    # Last fallback: generate one (still no logo/text).
    found = _pollinations_photo(topic)
    if found:
        log("info", f"photo: pollinations (generated) for '{topic}'")
        return found
    log("warning", f"photo: NONE found for '{topic}' -> topic dropped")
    return None


# ---------------------------------------------------------------- Bluesky trending (MOST IMPORTANT)
# News discovery starts HERE: what is trending on Bluesky decides what
# news gets written. Only if Bluesky trending is unavailable do we fall
# back to RSS top stories.
BSKY_PUBLIC = "https://public.api.bsky.app/xrpc"


def get_bluesky_trending(limit=10):
    """Return a list of trending topic strings from Bluesky."""
    topics = []
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.unspecced.getTrendingTopics",
                         timeout=20)
        if r.status_code == 200:
            for t in r.json().get("topics", [])[:limit]:
                name = (t.get("topic") or "").strip()
                if name:
                    topics.append(name)
            if topics:
                log("info", f"trending (bluesky): {topics[:5]}")
                return topics
    except Exception as e:
        log("warning", f"trending topics error: {e}")
    # Fallback: What's Hot feed -> pull hashtags/keywords from hot posts.
    try:
        feed_uri = ("at://did:plc:z72i7hdynmk6r22z27h6tvur/"
                    "app.bsky.feed.generator/whats-hot")
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getFeed",
                         params={"feed": feed_uri, "limit": 25}, timeout=20)
        if r.status_code == 200:
            seen = []
            for item in r.json().get("feed", []):
                text = ((item.get("post") or {}).get("record") or {}).get("text", "")
                for tag in re.findall(r"#(\w+)", text):
                    if tag.lower() not in [s.lower() for s in seen]:
                        seen.append(tag)
                if len(seen) >= limit:
                    break
            if seen:
                log("info", f"trending (whats-hot hashtags): {seen[:5]}")
                return seen
    except Exception as e:
        log("warning", f"whats-hot error: {e}")
    return []


def search_bluesky_posts(query, limit=10):
    """Search Bluesky posts (public, no login). Returns list of posts."""
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.searchPosts",
                         params={"q": query, "sort": "top", "limit": limit},
                         timeout=20)
        if r.status_code == 200:
            return r.json().get("posts", [])
    except Exception as e:
        log("warning", f"bluesky search error: {e}")
    return []


# ---------------------------------------------------------------- news verification
def verify_news(topic):
    """Check a topic against Google News RSS. Returns (verified, sources, items).
    Verified = at least 2 DIFFERENT sources report it (truth check)."""
    try:
        url = ("https://news.google.com/rss/search?q=" + quote_plus(topic) +
               "&hl=en&gl=US&ceid=US:en")
        r = requests.get(url, timeout=25,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200:
            return False, [], []
        root = ET.fromstring(r.content)
        items, sources = [], set()
        for item in root.findall(".//item"):
            title = (item.findtext("title") or "").strip()
            link = (item.findtext("link") or "").strip()
            src = (item.findtext("source") or "").strip()
            if not src and link:
                src = urlparse(link).netloc.replace("www.", "")
            if title and link:
                items.append({"title": title, "link": link, "source": src})
                if src:
                    sources.add(src.lower())
            if len(items) >= 8:
                break
        verified = len(sources) >= 2
        return verified, sorted(sources), items
    except Exception as e:
        log("warning", f"verify_news error: {e}")
        return False, [], []

# ---------------------------------------------------------------- Blogger
def blogger_publish(title, html_body, labels=None):
    """Publish an article to Blogger. Returns the post URL or None."""
    if not (BLOG_ID and BLOGGER_REFRESH_TOKEN and BLOGGER_CLIENT_ID
            and BLOGGER_CLIENT_SECRET):
        log("warning", "blogger_publish: Blogger credentials not configured")
        return None
    body = {"kind": "blogger#post", "blog": {"id": BLOG_ID},
            "title": title, "content": html_body,
            "labels": labels or ["News"]}
    if GOOGLE_AVAILABLE:
        try:
            creds = GoogleCredentials(
                token=None, refresh_token=BLOGGER_REFRESH_TOKEN,
                token_uri="https://oauth2.googleapis.com/token",
                client_id=BLOGGER_CLIENT_ID,
                client_secret=BLOGGER_CLIENT_SECRET,
                scopes=["https://www.googleapis.com/auth/blogger"])
            service = google_build("blogger", "v3", credentials=creds)
            post = service.posts().insert(blogId=BLOG_ID, body=body,
                                          isDraft=False).execute()
            return post.get("url")
        except Exception as e:
            log("warning", f"blogger publish (sdk) failed: {e}")
    # REST fallback (no google library needed).
    try:
        tok = requests.post("https://oauth2.googleapis.com/token",
                            data={"client_id": BLOGGER_CLIENT_ID,
                                  "client_secret": BLOGGER_CLIENT_SECRET,
                                  "refresh_token": BLOGGER_REFRESH_TOKEN,
                                  "grant_type": "refresh_token"}, timeout=20)
        access = tok.json().get("access_token")
        if not access:
            log("warning", "blogger publish: could not refresh access token")
            return None
        r = requests.post(
            f"https://blogger.googleapis.com/v3/blogs/{BLOG_ID}/posts",
            json=body, headers={"Authorization": f"Bearer {access}"}, timeout=30)
        if r.status_code in (200, 201):
            return r.json().get("url")
        log("warning", f"blogger publish (rest) {r.status_code}: {r.text[:200]}")
    except Exception as e:
        log("warning", f"blogger publish (rest) failed: {e}")
    return None


def blogger_posts_today():
    """How many posts were published to Blogger today (for the daily cap)."""
    conn = db_connect()
    try:
        row = conn.execute(
            "SELECT COUNT(*) c FROM posts WHERE substr(created_at,1,10)=?",
            (today_str(),)).fetchone()
        return row["c"] if row else 0
    finally:
        conn.close()


# ---------------------------------------------------------------- Bluesky client
def bsky_login(handle, app_password):
    if not ATPROTO_AVAILABLE:
        log("warning", "bluesky: atproto library not installed")
        return None
    try:
        client = AtprotoClient()
        client.login(handle, app_password)
        return client
    except Exception as e:
        log("warning", f"bluesky login failed for {handle}: {e}")
        return None


def bluesky_post(client, text, image_path=None, image_alt=""):
    """Post to Bluesky (URL in the text becomes a clickable link).
    Returns (uri, url) or None."""
    try:
        if image_path and os.path.exists(image_path):
            with open(image_path, "rb") as f:
                img = f.read()
            resp = client.send_image(text=text, image=img, image_alt=image_alt or text[:100])
        else:
            resp = client.send_post(text=text)
        uri = getattr(resp, "uri", "") or ""
        # Build a public bsky.app URL from the uri.
        url = ""
        if uri:
            parts = uri.split("/")
            if len(parts) >= 5:
                did, rkey = parts[2], parts[4]
                url = f"https://bsky.app/profile/{did}/post/{rkey}"
        return uri, url
    except Exception as e:
        log("warning", f"bluesky post failed: {e}")
        return None


def bluesky_reply(client, text, parent_uri, parent_cid, root_uri=None, root_cid=None):
    """Reply to a Bluesky post. Returns the reply uri or None."""
    try:
        from atproto import models
        root_uri = root_uri or parent_uri
        root_cid = root_cid or parent_cid
        ref = models.AppBskyFeedPost.ReplyRef(
            parent=models.ComAtprotoRepoStrongRef.Main(uri=parent_uri, cid=parent_cid),
            root=models.ComAtprotoRepoStrongRef.Main(uri=root_uri, cid=root_cid))
        resp = client.send_post(text=text, reply_to=ref)
        return getattr(resp, "uri", "") or ""
    except Exception as e:
        log("warning", f"bluesky reply failed: {e}")
        return None


def bluesky_own_posts_with_replies(client, handle, limit=5):
    """Our recent posts + their un-replied comments. Returns
    [{uri, cid, replies:[{uri, cid, author, text, created_at}]}]."""
    out = []
    try:
        feed = client.get_author_feed(actor=handle, limit=limit)
        for item in (feed.feed or []):
            post = item.post
            uri, cid = post.uri, post.cid
            try:
                thread = client.get_post_thread(uri=uri)
                replies = []
                for rep in (getattr(thread.thread, "replies", None) or []):
                    rp = getattr(rep, "post", None)
                    if rp is None:
                        continue
                    rec = getattr(rp, "record", None)
                    replies.append({
                        "uri": rp.uri, "cid": rp.cid,
                        "author": getattr(getattr(rp, "author", None), "handle", ""),
                        "text": getattr(rec, "text", "") if rec else "",
                        "created_at": getattr(rec, "created_at", "") if rec else "",
                    })
                out.append({"uri": uri, "cid": cid, "replies": replies})
            except Exception as e:
                log("warning", f"thread fetch failed for {uri}: {e}")
    except Exception as e:
        log("warning", f"author feed failed for {handle}: {e}")
    return out


def get_high_engagement_posts(limit=10):
    """Popular Bluesky posts worth replying to. Returns
    [{uri, cid, author, text, like_count, repost_count, reply_count}]."""
    posts = []
    # What's Hot feed is the best "high engagement" signal.
    try:
        feed_uri = ("at://did:plc:z72i7hdynmk6r22z27h6tvur/"
                    "app.bsky.feed.generator/whats-hot")
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getFeed",
                         params={"feed": feed_uri, "limit": 25}, timeout=20)
        if r.status_code == 200:
            for item in r.json().get("feed", []):
                p = item.get("post", {})
                posts.append({
                    "uri": p.get("uri", ""), "cid": p.get("cid", ""),
                    "author": (p.get("author") or {}).get("handle", ""),
                    "text": ((p.get("record") or {}).get("text") or "")[:200],
                    "like_count": p.get("likeCount", 0),
                    "repost_count": p.get("repostCount", 0),
                    "reply_count": p.get("replyCount", 0),
                })
    except Exception as e:
        log("warning", f"whats-hot feed error: {e}")
    if posts:
        posts.sort(key=lambda x: x["like_count"] + x["repost_count"] * 2,
                   reverse=True)
        return posts[:limit]
    # Fallback: search for popular posts.
    for p in search_bluesky_posts("breaking news", limit=limit):
        posts.append({"uri": p.get("uri", ""), "cid": p.get("cid", ""),
                      "author": (p.get("author") or {}).get("handle", ""),
                      "text": ((p.get("record") or {}).get("text") or "")[:200],
                      "like_count": p.get("likeCount", 0),
                      "repost_count": p.get("repostCount", 0),
                      "reply_count": p.get("replyCount", 0)})
    return posts


def get_fresh_comments(post_uri, minutes=5):
    """Comments on a post made within the last `minutes` minutes."""
    fresh = []
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getPostThread",
                         params={"uri": post_uri, "depth": 2}, timeout=20)
        if r.status_code != 200:
            return fresh
        cutoff = now_utc() - timedelta(minutes=minutes)
        thread = r.json().get("thread", {})
        for rep in thread.get("replies", []) or []:
            p = rep.get("post", {})
            rec = p.get("record", {})
            created = rec.get("createdAt", "")
            try:
                ts = datetime.fromisoformat(created.replace("Z", "+00:00"))
            except Exception:
                continue
            if ts >= cutoff:
                fresh.append({"uri": p.get("uri", ""), "cid": p.get("cid", ""),
                              "author": (p.get("author") or {}).get("handle", ""),
                              "text": (rec.get("text") or "")[:300],
                              "created_at": created})
    except Exception as e:
        log("warning", f"fresh comments error: {e}")
    return fresh


# ---------------------------------------------------------------- accounts
def list_accounts():
    """All Bluesky accounts: env secret first, then dashboard DB."""
    accounts = list(ENV_BLUESKY_ACCOUNTS)
    seen = {a["handle"] for a in accounts}
    try:
        conn = db_connect()
        try:
            rows = conn.execute(
                "SELECT handle, app_password, display_name FROM accounts "
                "WHERE active=1").fetchall()
        finally:
            conn.close()
        for r in rows:
            if r["handle"] not in seen:
                accounts.append({"handle": r["handle"],
                                 "app_password": r["app_password"],
                                 "display_name": r["display_name"] or ""})
                seen.add(r["handle"])
    except Exception:
        pass
    return accounts


# ---------------------------------------------------------------- article writing
ARTICLE_PROMPT = """You are a news writer for a news blog. Write a complete,
SEO-friendly news article in ENGLISH about this trending topic.

Topic: {topic}
Verified facts / sources:
{facts}

Rules:
- Start with a STRONG hook in the first 2 lines (clickbait style, but honest).
- Headline first, on its own line, starting with "HEADLINE: ".
- Then the article: 500-700 words, well organised with subheadings
  (use ## for subheadings), short paragraphs, bold key facts.
- Include a "Why it matters" section and a "What happens next" section.
- End with a "Sources:" line listing the source names.
- English only. No made-up quotes, numbers or claims - use only the facts
  given above. If a fact is unverified, say so.
"""

BSKY_POST_PROMPT = """Write ONE clickbait Bluesky post in ENGLISH about this news.
It must be different from the others (unique wording and angle).
Keep it under 250 characters. End with the blog link on its own line.
News: {headline}
Blog link: {link}
"""

REPLY_PROMPT = """Write ONE short, natural, relevant Bluesky reply in ENGLISH to
this comment. It must sound like a real person, not an ad. Do NOT repeat
the comment. Keep it under 200 characters. End with this link on its own
line: {link}

Comment: "{comment}"
Context (the post it was on): "{context}"
"""


def build_article_html(article_text, image_url, source_names):
    """Turn the Gemini article text into Blogger-ready HTML."""
    lines = [l.rstrip() for l in (article_text or "").splitlines()]
    html_parts = []
    for line in lines:
        if not line.strip():
            continue
        if line.startswith("HEADLINE:"):
            continue
        if line.startswith("## "):
            html_parts.append(f"<h2>{html_lib.escape(line[3:].strip())}</h2>")
        elif line.startswith("Sources:"):
            html_parts.append(
                f"<p><small><b>Sources:</b> {html_lib.escape(line[8:].strip())}</small></p>")
        else:
            # Bold **text** -> <b>text</b>
            esc = html_lib.escape(line)
            esc = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", esc)
            html_parts.append(f"<p>{esc}</p>")
    img = ""
    if image_url:
        img = (f'<p><img src="{html_lib.escape(image_url)}" alt="news photo" '
               f'style="width:100%;height:auto;" /></p>')
    return img + "\n".join(html_parts)


def extract_headline(article_text):
    for line in (article_text or "").splitlines():
        if line.strip().startswith("HEADLINE:"):
            return line.strip()[9:].strip()
    return (article_text or "").splitlines()[0][:120] if article_text else "Breaking News"

# ---------------------------------------------------------------- worker
try:
    from zoneinfo import ZoneInfo
    USER_TZ = ZoneInfo("Asia/Dhaka")
except Exception:  # pragma: no cover
    USER_TZ = timezone(timedelta(hours=6))

OWN_REPLY_PROMPT = """Write ONE short, warm, natural Bluesky reply in ENGLISH
to this comment on MY post. Sound like a real person. Keep it under 150
characters. Do not add any link.

Comment: "{comment}"
"""

WORKER_RUNNING = False


def candidate_topics(state, limit=5):
    """Trending topics from Bluesky FIRST (verified, not already posted).
    Falls back to RSS top stories if Bluesky trending is unavailable."""
    cands = []
    posted = [t.lower() for t in state.get("posted_topics", [])]
    # Forced topic (set from the dashboard) goes FIRST, if not already posted.
    forced = str(get_setting("force_topic", "") or "").strip()
    if forced and forced.lower() not in posted:
        verified, sources, items = verify_news(forced)
        if verified:
            facts = "\n".join(f"- {i['title']} ({i['source']})" for i in items[:5])
            cands.append((forced, sources, facts))
            log("info", f"forced topic queued: {forced}")
        else:
            log("info", f"forced topic not verified (needs 2 sources): {forced}")
    for topic in get_bluesky_trending(limit=10):
        if topic.lower() in posted:
            continue
        verified, sources, items = verify_news(topic)
        if verified:
            facts = "\n".join(f"- {i['title']} ({i['source']})" for i in items[:5])
            cands.append((topic, sources, facts))
        else:
            log("info", f"topic not verified (needs 2 sources): {topic}")
        if len(cands) >= limit:
            break
    if cands:
        return cands
    # Fallback: Google News top stories.
    try:
        r = requests.get("https://news.google.com/rss?hl=en&gl=US&ceid=US:en",
                         timeout=25, headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code == 200:
            root = ET.fromstring(r.content)
            for item in root.findall(".//item")[:10]:
                title = (item.findtext("title") or "").strip()
                if not title or title.lower() in posted:
                    continue
                verified, sources, items = verify_news(title)
                if verified:
                    facts = "\n".join(f"- {i['title']} ({i['source']})"
                                      for i in items[:5])
                    cands.append((title, sources, facts))
                if len(cands) >= limit:
                    break
    except Exception as e:
        log("warning", f"rss fallback error: {e}")
    return cands


def record_post(title, url, topic, source, image_url):
    conn = db_connect()
    try:
        conn.execute(
            "INSERT INTO posts(title, url, topic, source, image_url, status, created_at) "
            "VALUES(?, ?, ?, ?, ?, 'published', ?)",
            (title, url, topic, source, image_url, now_iso()))
        conn.commit()
    finally:
        conn.close()


def run_blogger_cycle(state):
    """Write + publish ONE article from a Bluesky-trending topic.
    Returns the article dict or None."""
    cap = int(get_setting("blogger_daily_limit", str(DEFAULT_BLOGGER_DAILY_LIMIT)) or 0)
    if cap > 0 and blogger_posts_today() >= cap:
        log("info", f"blogger daily cap reached ({cap}/day) - skipping publish")
        return None
    for topic, sources, facts in candidate_topics(state, limit=5)[:3]:
        article_text = ai_write(ARTICLE_PROMPT.format(topic=topic, facts=facts),
                                max_tokens=2000)
        if not article_text:
            log("warning", f"article writing failed for '{topic}'")
            continue
        headline = extract_headline(article_text)
        # STRICT RULE: no photo = no post. Drop this topic, try the next.
        photo = fetch_photo(topic)
        if not photo:
            state.setdefault("posted_topics", []).append(topic.lower())
            log("warning", f"topic dropped (no photo): {topic}")
            continue
        html_body = build_article_html(article_text,
                                       photo.get("url", ""),
                                       ", ".join(sources))
        url = blogger_publish(headline, html_body, labels=["News"])
        if not url:
            log("warning", f"blogger publish failed for '{headline}'")
            continue
        record_post(headline, url, topic, ", ".join(sources), photo.get("url", ""))
        state.setdefault("posted_urls", []).append(url)
        state.setdefault("posted_topics", []).append(topic.lower())
        log("info", f"published: {headline} -> {url}")
        return {"title": headline, "url": url,
                "image_path": photo.get("local_path", ""),
                "image_url": photo.get("url", ""), "topic": topic}
    log("info", "blogger cycle: no publishable topic this run")
    return None


def latest_article():
    conn = db_connect()
    try:
        row = conn.execute("SELECT title, url, image_url FROM posts "
                           "ORDER BY id DESC LIMIT 1").fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def replies_today():
    conn = db_connect()
    try:
        row = conn.execute(
            "SELECT COUNT(*) c FROM replies WHERE substr(created_at,1,10)=?",
            (today_str(),)).fetchone()
        return row["c"] if row else 0
    finally:
        conn.close()


def record_reply(post_uri, comment_uri, reply_text, account_handle):
    conn = db_connect()
    try:
        conn.execute(
            "INSERT INTO replies(post_uri, comment_uri, reply_text, account_handle, "
            "status, created_at) VALUES(?, ?, ?, ?, 'sent', ?)",
            (post_uri, comment_uri, reply_text, account_handle, now_iso()))
        conn.commit()
    finally:
        conn.close()


def run_bluesky_cycle(state, article=None):
    """Post to Bluesky accounts (unique post per account) + replies."""
    accounts = list_accounts()
    if not accounts:
        log("info", "bluesky cycle: no accounts configured")
        return
    article = article or latest_article()
    if not article:
        log("info", "bluesky cycle: no article to link yet")
        return
    per_run = int(get_setting("bsky_posts_per_run", str(DEFAULT_BSKY_POSTS_PER_RUN)) or 1)
    state.setdefault("bsky_posted", [])
    # --- 1) One UNIQUE post per account (same post never goes to all accounts).
    for acc in accounts:
        key = f"{acc['handle']}|{article['url']}"
        if key in state["bsky_posted"]:
            continue
        client = bsky_login(acc["handle"], acc["app_password"])
        if not client:
            continue
        text = ai_write(BSKY_POST_PROMPT.format(headline=article["title"],
                                                link=article["url"]),
                        max_tokens=400)
        if not text:
            text = f"{article['title']}\n{article['url']}"
        img = article.get("image_path") or ""
        posted = bluesky_post(client, text,
                              image_path=img if img and os.path.exists(img) else None,
                              image_alt=article["title"][:100])
        if posted:
            state["bsky_posted"].append(key)
            log("info", f"bluesky posted ({acc['handle']}): {posted[1]}")
        time.sleep(5)
    # --- 2) Replies to fresh comments on high-engagement posts.
    # 0 = UNLIMITED (user's choice). 429 auto-pause still protects the accounts.
    daily_cap = int(get_setting("bsky_reply_daily_cap", str(DEFAULT_BSKY_REPLY_DAILY_CAP)) or 0)
    per_run_replies = int(get_setting("bsky_reply_per_run", str(DEFAULT_BSKY_REPLY_PER_RUN)) or 0)
    gap = int(get_setting("reply_gap_seconds", str(DEFAULT_REPLY_GAP_SECONDS)) or 0)
    state.setdefault("replied_comments", [])
    done_replies = 0
    def under_daily_cap():
        return daily_cap <= 0 or replies_today() < daily_cap
    def under_run_cap():
        return per_run_replies <= 0 or done_replies < per_run_replies
    if under_daily_cap():
        hot = get_high_engagement_posts(limit=5)
        acc_idx = 0
        for post in hot:
            if not under_run_cap() or not under_daily_cap():
                break
            for comment in get_fresh_comments(post["uri"], minutes=5):
                if not under_run_cap() or not under_daily_cap():
                    break
                if comment["uri"] in state["replied_comments"]:
                    continue
                acc = accounts[acc_idx % len(accounts)]
                acc_idx += 1
                client = bsky_login(acc["handle"], acc["app_password"])
                if not client:
                    continue
                reply_text = groq_text(REPLY_PROMPT.format(
                    link=article["url"], comment=comment["text"],
                    context=post["text"]), max_tokens=400)
                if not reply_text:
                    continue
                uri = bluesky_reply(client, reply_text, comment["uri"],
                                    comment["cid"], post["uri"], post["cid"])
                if uri:
                    state["replied_comments"].append(comment["uri"])
                    record_reply(post["uri"], comment["uri"], reply_text, acc["handle"])
                    done_replies += 1
                    log("info", f"replied ({acc['handle']}) to {comment['author']}")
                    if gap > 0:
                        time.sleep(gap)
    # --- 3) Reply to ALL comments on our OWN posts.
    for acc in accounts:
        if per_run_replies > 0 and done_replies >= per_run_replies + 5:
            break
        client = bsky_login(acc["handle"], acc["app_password"])
        if not client:
            continue
        for own in bluesky_own_posts_with_replies(client, acc["handle"], limit=3):
            for comment in own["replies"]:
                if comment["uri"] in state["replied_comments"]:
                    continue
                if comment["author"] == acc["handle"]:
                    continue
                reply_text = groq_text(OWN_REPLY_PROMPT.format(comment=comment["text"]),
                                       max_tokens=300)
                if not reply_text:
                    continue
                uri = bluesky_reply(client, reply_text, comment["uri"],
                                    comment["cid"], own["uri"], own["cid"])
                if uri:
                    state["replied_comments"].append(comment["uri"])
                    record_reply(own["uri"], comment["uri"], reply_text, acc["handle"])
                    done_replies += 1
                    log("info", f"replied to own-post comment ({acc['handle']})")


def next_run_for_card(card):
    raw = card.get("schedule_times") or []
    if isinstance(raw, str):
        try:
            times = json.loads(raw)
        except Exception:
            times = []
    else:
        times = raw if isinstance(raw, list) else []
    now_local = now_utc().astimezone(USER_TZ)
    if times:
        candidates = []
        for t in times:
            try:
                hh, mm = [int(x) for x in str(t).split(":")]
                cand = now_local.replace(hour=hh, minute=mm, second=0, microsecond=0)
                if cand <= now_local:
                    cand += timedelta(days=1)
                candidates.append(cand)
            except Exception:
                continue
        if candidates:
            return min(candidates).astimezone(UTC).isoformat()
    interval = int(card.get("interval_minutes") or 30)
    return (now_utc() + timedelta(minutes=interval)).isoformat()


CARDS_PATH = os.path.join(DATA_DIR, "cards.json")


def load_file_cards():
    """Cards from data/cards.json (edited via the dashboard / GitHub).
    This is the GitHub-only control panel - no server needed."""
    if not os.path.exists(CARDS_PATH):
        return []
    try:
        with open(CARDS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return [c for c in data if isinstance(c, dict)]
    except Exception as e:
        log("warning", f"cards.json load failed: {e}")
    return []


def file_card_due(card, state):
    """Is a file-based card due? Uses schedule_times (Dhaka) or the
    interval since its last run (tracked in state.json)."""
    runs = state.get("file_card_runs", {})
    last = runs.get(card.get("name", ""))
    last_dt = None
    if last:
        try:
            last_dt = datetime.fromisoformat(last)
            if last_dt.tzinfo is None:
                last_dt = last_dt.replace(tzinfo=UTC)
        except Exception:
            last_dt = None
    raw = card.get("schedule_times") or []
    times = raw if isinstance(raw, list) else []
    if times:
        now_local = now_utc().astimezone(USER_TZ)
        recent = None
        for t in times:
            try:
                hh, mm = [int(x) for x in str(t).split(":")]
                cand = now_local.replace(hour=hh, minute=mm, second=0, microsecond=0)
                if cand <= now_local and (recent is None or cand > recent):
                    recent = cand
            except Exception:
                continue
        if recent is None:
            return False
        if last_dt is None:
            return True
        return last_dt.astimezone(USER_TZ) < recent
    if last_dt is None:
        return True
    interval = int(card.get("interval_minutes") or 30)
    return now_utc() >= last_dt + timedelta(minutes=interval)


def execute_card(card, state):
    """Run one manual card once. Returns True on success."""
    ctype = card["type"]
    try:
        if ctype == "blogger_post":
            article = run_blogger_cycle(state)
            ok = article is not None
        elif ctype == "bluesky_post":
            article = latest_article()
            if not article:
                log("warning", f"card '{card['name']}': no article to post")
                return False
            accs = [a for a in list_accounts()
                    if not card.get("account_handle") or
                    a["handle"] == card["account_handle"]]
            ok = False
            for acc in accs[:1]:
                client = bsky_login(acc["handle"], acc["app_password"])
                if not client:
                    continue
                text = card.get("text") or ai_write(
                    BSKY_POST_PROMPT.format(headline=article["title"],
                                            link=article["url"]), max_tokens=400)
                if not text:
                    text = f"{article['title']}\n{article['url']}"
                if bluesky_post(client, text):
                    ok = True
        elif ctype == "bluesky_reply":
            article = latest_article()
            if not article:
                return False
            run_bluesky_cycle(state, article=article)
            ok = True
        else:
            log("warning", f"card '{card['name']}': unknown type {ctype}")
            return False
    except Exception as e:
        log("error", f"card '{card['name']}' failed: {e}")
        return False
    if card.get("id"):
        conn = db_connect()
        try:
            conn.execute(
                "UPDATE cards SET done_count=done_count+1, last_run=?, next_run=?, "
                "updated_at=? WHERE id=?",
                (now_iso(), next_run_for_card(card), now_iso(), card["id"]))
            conn.commit()
        finally:
            conn.close()
    else:
        # File-based card (data/cards.json): track last run in state.json.
        runs = state.setdefault("file_card_runs", {})
        runs[card.get("name", "")] = now_iso()
    log("info", f"card '{card['name']}' ran ({'ok' if ok else 'no-op'})")
    return ok


def run_cards_cycle(state):
    conn = db_connect()
    try:
        rows = conn.execute(
            "SELECT * FROM cards WHERE status='active'").fetchall()
        cards = [dict(r) for r in rows]
    finally:
        conn.close()
    for card in cards:
        nxt = card.get("next_run") or ""
        if nxt and nxt > now_iso():
            continue
        execute_card(card, state)
    # File-based cards (data/cards.json) - the GitHub-only control panel.
    for card in load_file_cards():
        if (card.get("status") or "active") != "active":
            continue
        if not file_card_due(card, state):
            continue
        execute_card(card, state)


def run_worker():
    global WORKER_RUNNING
    if WORKER_RUNNING:
        log("info", "worker already running - skipping")
        return
    WORKER_RUNNING = True
    init_db()
    state = load_state()
    state["runs"] = state.get("runs", 0) + 1
    state["last_run"] = now_iso()
    log("info", f"worker run #{state['runs']} started")
    paused = str(get_setting("paused", "false")).strip().lower() == "true"
    if paused:
        log("info", "automation is PAUSED (paused=true in config) - skipping all cycles")
    else:
        try:
            article = run_blogger_cycle(state)
        except Exception as e:
            log("error", f"blogger cycle failed: {e}")
            article = None
        try:
            run_bluesky_cycle(state, article=article)
        except Exception as e:
            log("error", f"bluesky cycle failed: {e}")
        try:
            run_cards_cycle(state)
        except Exception as e:
            log("error", f"cards cycle failed: {e}")
    save_state(state)
    append_logs_json()
    write_dashboard_json(state)
    WORKER_RUNNING = False
    log("info", "worker run finished")


# ---------------------------------------------------------------- web routes
def require_login():
    if not session.get("authed"):
        return jsonify({"error": "login required"}), 401
    return None


@app.route("/")
def index():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/images/<path:filename>")
def serve_image(filename):
    return send_from_directory(IMAGES_DIR, filename)


@app.route("/health")
def health():
    return jsonify({"status": "ok", "time": now_iso()})


@app.route("/api/login", methods=["POST"])
def api_login():
    data = request.get_json(silent=True) or {}
    if str(data.get("password", "")) == ADMIN_PASSWORD:
        session["authed"] = True
        return jsonify({"ok": True})
    return jsonify({"error": "wrong password"}), 401


@app.route("/api/logout", methods=["POST"])
def api_logout():
    session.clear()
    return jsonify({"ok": True})


@app.route("/api/me")
def api_me():
    return jsonify({"authenticated": bool(session.get("authed"))})


@app.route("/api/status")
def api_status():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        cards = [dict(r) for r in conn.execute(
            "SELECT * FROM cards ORDER BY id DESC").fetchall()]
        accounts = [dict(r) for r in conn.execute(
            "SELECT id, handle, display_name, active, created_at FROM accounts "
            "ORDER BY id").fetchall()]
        logs = [dict(r) for r in conn.execute(
            "SELECT level, message, created_at FROM logs ORDER BY id DESC LIMIT 50"
            ).fetchall()]
        total_posts = conn.execute("SELECT COUNT(*) c FROM posts").fetchone()["c"]
        total_replies = conn.execute("SELECT COUNT(*) c FROM replies").fetchone()["c"]
    finally:
        conn.close()
    state = load_state()
    settings = {k: get_setting(k, "") for k in
                ("blogger_daily_limit", "bsky_reply_per_run",
                 "bsky_reply_daily_cap", "reply_gap_seconds", "bsky_posts_per_run")}
    return jsonify({
        "stats": {"blogger_today": blogger_posts_today(),
                  "replies_today": replies_today(),
                  "total_posts": total_posts, "total_replies": total_replies,
                  "accounts": len(list_accounts()),
                  "last_run": state.get("last_run", ""),
                  "runs": state.get("runs", 0)},
        "cards": cards, "accounts": accounts, "logs": logs,
        "settings": settings,
    })


@app.route("/api/trending")
def api_trending():
    err = require_login()
    if err:
        return err
    return jsonify({"topics": get_bluesky_trending(limit=10)})


@app.route("/api/cards", methods=["GET", "POST"])
def api_cards():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "GET":
            rows = conn.execute("SELECT * FROM cards ORDER BY id DESC").fetchall()
            return jsonify({"cards": [dict(r) for r in rows]})
        data = request.get_json(silent=True) or {}
        name = (data.get("name") or "Card").strip()
        ctype = data.get("type") or "bluesky_post"
        if ctype not in ("bluesky_post", "bluesky_reply", "blogger_post"):
            return jsonify({"error": "bad type"}), 400
        times = data.get("schedule_times") or []
        if isinstance(times, str):
            times = [t.strip() for t in times.split(",") if t.strip()]
        cur = conn.execute(
            "INSERT INTO cards(name, type, link, account_handle, count, "
            "interval_minutes, schedule_times, text, status, created_at, updated_at) "
            "VALUES(?, ?, ?, ?, ?, ?, ?, ?, 'active', ?, ?)",
            (name, ctype, data.get("link", ""), data.get("account_handle", ""),
             int(data.get("count") or 1), int(data.get("interval_minutes") or 30),
             json.dumps(times), data.get("text", ""), now_iso(), now_iso()))
        conn.commit()
        return jsonify({"ok": True, "id": cur.lastrowid})
    finally:
        conn.close()


@app.route("/api/cards/<int:cid>", methods=["PUT", "DELETE"])
def api_card_one(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "DELETE":
            conn.execute("DELETE FROM cards WHERE id=?", (cid,))
            conn.commit()
            return jsonify({"ok": True})
        data = request.get_json(silent=True) or {}
        fields = {}
        for key in ("name", "type", "link", "account_handle", "text", "status"):
            if key in data:
                fields[key] = data[key]
        for key in ("count", "interval_minutes"):
            if key in data:
                fields[key] = int(data[key] or 0)
        if "schedule_times" in data:
            times = data["schedule_times"]
            if isinstance(times, str):
                times = [t.strip() for t in times.split(",") if t.strip()]
            fields["schedule_times"] = json.dumps(times)
        if not fields:
            return jsonify({"error": "nothing to update"}), 400
        fields["updated_at"] = now_iso()
        sets = ", ".join(f"{k}=?" for k in fields)
        conn.execute(f"UPDATE cards SET {sets} WHERE id=?",
                     (*fields.values(), cid))
        conn.commit()
        return jsonify({"ok": True})
    finally:
        conn.close()


@app.route("/api/cards/<int:cid>/run", methods=["POST"])
def api_card_run(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        row = conn.execute("SELECT * FROM cards WHERE id=?", (cid,)).fetchone()
        card = dict(row) if row else None
    finally:
        conn.close()
    if not card:
        return jsonify({"error": "card not found"}), 404
    state = load_state()
    ok = execute_card(card, state)
    save_state(state)
    return jsonify({"ok": ok})


@app.route("/api/cards/<int:cid>/pause", methods=["POST"])
def api_card_pause(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='paused', updated_at=? WHERE id=?",
                     (now_iso(), cid))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/cards/<int:cid>/resume", methods=["POST"])
def api_card_resume(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='active', updated_at=? WHERE id=?",
                     (now_iso(), cid))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/pause-all", methods=["POST"])
def api_pause_all():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='paused', updated_at=?", (now_iso(),))
        conn.commit()
    finally:
        conn.close()
    log("info", "pause-all: every card paused")
    return jsonify({"ok": True})


@app.route("/api/accounts", methods=["GET", "POST"])
def api_accounts():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "GET":
            rows = conn.execute(
                "SELECT id, handle, display_name, active, created_at FROM accounts "
                "ORDER BY id").fetchall()
            return jsonify({"accounts": [dict(r) for r in rows]})
        data = request.get_json(silent=True) or {}
        handle = (data.get("handle") or "").strip()
        pw = (data.get("app_password") or "").strip()
        if not handle or not pw:
            return jsonify({"error": "handle and app password required"}), 400
        cur = conn.execute(
            "INSERT INTO accounts(handle, app_password, display_name, created_at) "
            "VALUES(?, ?, ?, ?) ON CONFLICT(handle) DO UPDATE SET "
            "app_password=excluded.app_password, display_name=excluded.display_name",
            (handle, pw, data.get("display_name", ""), now_iso()))
        conn.commit()
        return jsonify({"ok": True, "id": cur.lastrowid})
    finally:
        conn.close()


@app.route("/api/accounts/<int:aid>", methods=["DELETE"])
def api_account_delete(aid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("DELETE FROM accounts WHERE id=?", (aid,))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/settings", methods=["GET", "POST"])
def api_settings():
    err = require_login()
    if err:
        return err
    keys = ("blogger_daily_limit", "bsky_reply_per_run",
            "bsky_reply_daily_cap", "reply_gap_seconds", "bsky_posts_per_run")
    if request.method == "GET":
        return jsonify({k: get_setting(k, "") for k in keys})
    data = request.get_json(silent=True) or {}
    for k in keys:
        if k in data:
            set_setting(k, data[k])
    return jsonify({"ok": True})


@app.route("/api/run-worker", methods=["POST"])
def api_run_worker():
    err = require_login()
    if err:
        return err
    if WORKER_RUNNING:
        return jsonify({"ok": False, "error": "worker already running"})
    t = threading.Thread(target=run_worker, daemon=True)
    t.start()
    return jsonify({"ok": True, "message": "worker started"})


@app.route("/api/export")
def api_export():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        cards = [dict(r) for r in conn.execute("SELECT * FROM cards").fetchall()]
        accounts = [dict(r) for r in conn.execute(
            "SELECT handle, display_name FROM accounts").fetchall()]
    finally:
        conn.close()
    settings = {k: get_setting(k, "") for k in
                ("blogger_daily_limit", "bsky_reply_per_run",
                 "bsky_reply_daily_cap", "reply_gap_seconds", "bsky_posts_per_run")}
    return jsonify({"cards": cards, "accounts": accounts, "settings": settings,
                    "exported_at": now_iso()})


# ---------------------------------------------------------------- entrypoint
init_db()

if __name__ == "__main__":
    if "--worker" in sys.argv:
        run_worker()
    else:
        port = int(os.environ.get("PORT", "5000"))
        print(f"Automation Website running on http://0.0.0.0:{port}", flush=True)
        app.run(host="0.0.0.0", port=port)
