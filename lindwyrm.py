#!/usr/bin/python
"""
+------------+
|  LINDWYRM  |
+------------+

"Here be dragons. Handled."
"""

# ========== IMPORTS ==========
import json
import logging
import os
import subprocess
import zlib
from bisect import bisect_right
from collections import OrderedDict
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache, partial, singledispatch
from heapq import heappush, heappushpop
from logging.handlers import SysLogHandler
from select import select
from shlex import split as shlex_split
from shutil import which
from signal import SIGINT, SIGTERM, signal
from sys import intern
from threading import Lock
from time import time
from typing import Any, NamedTuple
from urllib.parse import quote_from_bytes
import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore[missing-module-attribute]

try:
	import tomllib
except ModuleNotFoundError:
	import tomli as tomllib

# ========== PROGRAM NAME & LOG LEVEL ==========
PROG_NAME = "lindwyrm"
LOG_LVL = "INFO"

# ========== CONFIGURATION AND PATHS ==========
CONFIG_FILE = os.path.join(GLib.get_user_config_dir(), PROG_NAME, "config.toml")
CACHE_FILE = os.path.join(GLib.get_user_cache_dir(), PROG_NAME, "cache.json.zlib")
USER_UID = os.getuid()

# ========== GLOBAL CONSTANTS ==========
DBUS_BUSNAME = f"org.kde.{PROG_NAME}"
IFACE_KRUNNER = "org.kde.krunner1"
IO_CHUNK_SIZE = 131072
MAX_TOTAL_RESULTS = 800
ICON_UNKNOWN = intern("unknown")
TYPE_FILE = intern("FILE")
TYPE_FOLDER = intern("FOLDER")
TYPE_OCTET = intern("OCTET-STREAM")
MIME_URI = "text/uri-list"
MIME_TEXT = "text/plain"

# Formatting constants
_TIME_TH = [60, 3600, 86400, 604800, 2629746, 31556952]
_TIME_UN = ["minute", "hour", "day", "week", "month", "year"]
_SIZE_TH = [1, 1024, 1048576, 1073741824, 1099511627776]
_SIZE_UN = ["B", "KiB", "MiB", "GiB", "TiB"]
_CATEG_TH = [5, 20, 40, 60, 85]
_CATEG_MR = [0, 10, 30, 50, 70, 100]

# Magic detection
MAGICMIME = False
try:
	from magic import from_file as magic_from_file

	MAGICMIME = True
except ModuleNotFoundError:
	pass

CLIPBOARD_PROVIDERS = {
	MIME_URI: [
		("xclip", "-selection", "clipboard", "-t", MIME_URI),
		("wl-copy", "--type", MIME_URI),
	],
	MIME_TEXT: [
		("xclip", "-selection", "clipboard", "-in"),
		("wl-copy",),
		("xsel", "--clipboard", "--input"),
	],
}


# ========== NAMED TUPLES ==========
class LightResult(NamedTuple):
	path: str
	icon: str
	subtext: str
	score: float


class RelevanceWeights(NamedTuple):
	half_life: float
	mod_time: float
	depth: float
	exec_bonus: float
	dir_bonus: float


# ========== SYSLOG LOGGING ==========
syslog_extension = (
	("EMERGENCY", 70, "emerg"),
	("ALERT", 60, "alert"),
	("NOTICE", 25, "notice"),
)

for level_name, level_value, _ in syslog_extension:
	setattr(logging, level_name, level_value)
	logging.addLevelName(level_value, level_name)
	setattr(
		logging.Logger,
		level_name.lower(),
		lambda self, msg, lvl=level_value, *args, **kws: (
			self._log(lvl, msg, args, **kws) if self.isEnabledFor(lvl) else None
		),
	)

logger = logging.getLogger(PROG_NAME)
log_level = os.getenv(f"{PROG_NAME.upper()}_LOG_LEVEL", LOG_LVL)
logger.setLevel(getattr(logging, log_level, logging.INFO))
sockets = ["/dev/log", "/var/run/syslog"]

if not (addr := next((p for p in sockets if os.path.exists(p)), None)):
	msg = f"No syslog socket found. Tried: {sockets}"
	raise RuntimeError(msg)

handler = SysLogHandler(address=addr)
handler.priority_map.update({i[0]: i[2] for i in syslog_extension})
handler.setFormatter(
	logging.Formatter(f"{PROG_NAME}[%(process)d]: %(levelname)s - %(message)s"),
)
logger.addHandler(handler)
logger.notice(
	f"{PROG_NAME.capitalize()} started successfully: (UID={USER_UID}, log_lvl={logging.getLevelName(logger.level)})"
)


# ========== HELPER FUNCTIONS - VALIDATION ==========
def _verify_access_impl(path: str, flags: int, mode: int | None = None, st_mode_mask: int = 0o177) -> int:
	fd = os.open(path, flags, *([] if mode is None else [mode]))
	st = os.fstat(fd)
	if st.st_uid != USER_UID or (st.st_mode & st_mode_mask):
		os.close(fd)
		b_path = os.path.basename(path)
		t_mode = f"{0o777 - st_mode_mask:#o}"[2:]
		msg = f"SECURITY VIOLATION: '{path}' has incorrect ownership or permissions\
\n(UID {st.st_uid} mode {st.st_mode & 0o777:#o}, expected UID {USER_UID} mode 0o{t_mode})\
, Do `chown $USER {b_path}` and `chmod {t_mode} {b_path}` in parent dir."
		raise PermissionError(msg)

	return fd


_verify_dir_access = partial(_verify_access_impl, flags=os.O_RDONLY | os.O_DIRECTORY, st_mode_mask=0o077)
_verify_file_access = partial(_verify_access_impl, flags=os.O_RDONLY | os.O_NOFOLLOW)
_verify_file_write = partial(
	_verify_access_impl, flags=os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, mode=0o600
)


def intern_pair(a: str, b: str) -> tuple[str, str]:
	return intern(a), intern(b)


def validate_str(text: str | bytes) -> str | None:
	if isinstance(text, bytes):
		try:
			text = os.fsdecode(text)
		except (UnicodeDecodeError, ValueError):
			return None

	if "\x00" in text:
		return None

	return text


# ========== HELPER FUNCTIONS - CONFIGURATION ==========
def read_config(path: str) -> dict[str, Any]:
	try:
		_verify_dir_access(os.path.dirname(path))
		fd = _verify_file_access(path)
		with os.fdopen(fd, "rb") as f:
			data = tomllib.load(f)

		logger.info(f"Configuration loaded successfully from '{path}'")
		logger.debug(f"Config keys: {list(data.keys())}")
		return {**data, **data.get("settings", {})}
	except FileNotFoundError:
		logger.info(f"Config file not found at '{path}', using defaults")
		return {}
	except PermissionError:
		logger.exception(f"Permission error loading config from '{path}'")
		return {}
	except (OSError, ValueError):
		logger.exception(f"Failed to load config from '{path}'")
		return {}
	except tomllib.TOMLDecodeError:
		logger.exception(f"Invalid TOML syntax in '{path}'")
		return {}


# ========== CONFIGURATION ==========
_GLOBAL_CFG = read_config(CONFIG_FILE)
CACHE_MED = int(_GLOBAL_CFG.get("cache_med", 4096))
CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", 8192))
# SUBPROC_TO = int(_GLOBAL_CFG.get("subprocess_timeout", 2))
logger.debug(f"Cache sizes - Medium: {CACHE_MED}, Big: {CACHE_BIG}")


def get_config_value(cfg: dict, key: str, default: Any, type_fn: Callable = str) -> Any:
	"""Extracts and validates configuration values."""
	try:
		value = type_fn(cfg.get(key, default))
		if value != default:
			logger.debug(f"Config override: {key} = {value}")

		return value
	except (TypeError, ValueError) as e:
		logger.warning(f"Invalid config value for '{key}': {cfg.get(key)}, using default: {default} ({e})")
		return default


def create_normalizer(h: Callable[[str], list]) -> Callable[[Any], list]:
	normalizer = singledispatch(lambda _: [])
	normalizer.register(list, list)
	normalizer.register(str, h)
	return normalizer


normalize_shlex = create_normalizer(shlex_split)
normalize_list = create_normalizer(lambda v: [v])


def get_command_list(cfg: dict, key: str, default: list) -> list:
	"""Obtains list of commands from config or searches for binaries."""
	val = cfg.get(key)
	if val is None:
		if default == []:
			logger.debug(f"No default commands provided for '{key}', skipping...")
			return []
		if found := _find_command(*default):
			logger.debug(f"Using detected command for '{key}': {found}")
			return found

		logger.warning(f"No command found for '{key}' (tried: {default})")
		return []

	result = normalize_shlex(val)
	logger.debug(f"Using configured command for '{key}': {result}")
	return result


# ========== HELPER FUNCTIONS - SYSTEM ==========
def _find_command(*candidates: str | list[str]) -> list[str] | None:
	for cmd in candidates:
		cmdx = normalize_list(cmd)
		if found := which(cmdx[0]):
			logger.debug(f"Found command '{cmd}' at: {found}")
			cmdx[0] = found
			return cmdx

	logger.debug(f"None of these commands found: {candidates}")
	return None


def _spawn(cmd: list[str]) -> None:
	try:
		subprocess.Popen(
			cmd,
			stdout=subprocess.DEVNULL,
			stderr=subprocess.DEVNULL,
			stdin=subprocess.DEVNULL,
			start_new_session=True,
		)
		logger.debug(f"Spawned process: {cmd}")
	except (OSError, subprocess.SubprocessError):
		logger.warning(f"Failed to spawn process {cmd}")


def _run_subprocess_input(cmd: list[str], text_input: str) -> bool:
	try:
		subprocess.run(
			cmd,
			input=text_input.encode("utf-8", errors="surrogateescape"),
			check=True,
			capture_output=True,
			timeout=2,
		)
		logger.debug(f"Subprocess succeeded: {cmd[0]}")
		return True
	except subprocess.TimeoutExpired:
		if cmd[0] == "xclip":
			logger.debug("Subprocess succeeded: xclip")
			return True

		logger.warning(f"Subprocess timeout after 2s: {cmd}")
		return False
	except subprocess.CalledProcessError as e:
		logger.warning(f"Subprocess failed with exit code {e.returncode}: {cmd}")
		logger.debug(f"Subprocess stderr: {e.stderr.decode(errors='ignore')[:200]}")
		return False
	except (OSError, UnicodeEncodeError):
		logger.warning(f"Subprocess error for {cmd}")
		return False


# ========== HELPER FUNCTIONS - FORMATTING ==========
def human_readable_size(size: int) -> str:
	if size == 0:
		return "0 B"

	idx = bisect_right(_SIZE_TH, size) - 1
	return f"{size / _SIZE_TH[idx]:.1f} {_SIZE_UN[idx]}"


def human_readable_time(mtime: float | None, now: float) -> str:
	if mtime is None:
		return ""

	if (d := max(0, now - mtime)) < 60:
		return "Just now"

	idx = bisect_right(_TIME_TH, d) - 1
	return f"{(v := d / _TIME_TH[idx]):.1f} {_TIME_UN[idx]}{'s' * (v >= 2)} ago"


# ========== HELPER FUNCTIONS - METADATA (cached) ==========
@lru_cache(maxsize=CACHE_BIG)
def get_raw_stat(path: str) -> tuple[bool, float | None, int, int]:
	try:
		stat_info = os.stat(path, follow_symlinks=True)
		return ((stat_info.st_mode & 0o170000) == 0o040000, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode)
	except FileNotFoundError:
		logger.debug(f"File not found (stat): {path}")
		return False, None, 0, 0
	except (OSError, ValueError):
		logger.debug(f"Stat error for {path}")
		return False, None, 0, 0


@lru_cache(maxsize=CACHE_MED)
def get_display_metadata(path: str) -> tuple[str, str]:
	is_dir, mtime, size, _ = get_raw_stat(path)
	if mtime is None and size == 0:
		return "", ""

	return ("" if is_dir else human_readable_size(size), human_readable_time(mtime, time()))


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime = magic_from_file(path, mime=True)
		logger.debug(f"Magic MIME for {path}: {mime}")
		return intern_pair(mime.replace("/", "-"), mime)
	except (OSError, ValueError):
		logger.debug(f"Magic MIME detection failed for {path}")
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed, _ = Gio.content_type_guess(filename, None)
		if guessed == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			return intern_pair(ICON_UNKNOWN, ext[1:].upper() or TYPE_OCTET)

		icon_theme = Gio.content_type_get_icon(guessed)
		name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else ICON_UNKNOWN
		return intern_pair(name, guessed)
	except (GLib.GError, TypeError, AttributeError):
		logger.debug(f"Icon detection error for {filename}")
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _ = get_raw_stat(path)
	nice_size, nice_date = get_display_metadata(path)
	if is_dir:
		subtext = f"{TYPE_FOLDER} \U00002022 {nice_date}" if nice_date else TYPE_FOLDER
		return intern_pair("folder", subtext)

	icon, type_str = get_icon_for_extension(os.path.basename(path))
	if type_str == TYPE_OCTET and MAGICMIME:
		m_icon, m_type = cached_magic_mime(path)
		if m_icon != ICON_UNKNOWN:
			icon, type_str = m_icon, m_type

	parts = [type_str.split("/")[-1].upper()]
	parts.extend(filter(None, [nice_size, nice_date]))
	return icon, " \U00002022 ".join(parts)


# ========== HELPER FUNCTIONS - D-BUS ==========
def build_dbus_response(results: list[LightResult]) -> list:
	"""Build response in D-Bus format for KRunner."""
	return [
		(
			r.path,
			os.path.splitext(os.path.basename(r.path))[0].removesuffix('.tar'),
			r.icon,
			_CATEG_MR[bisect_right(_CATEG_TH, r.score * 100)],
			r.score,
			{"subtext": r.subtext},
		)
		for r in results[:MAX_TOTAL_RESULTS]
	]


# ========== CLASSES ==========
class RelevanceScorer:
	"""Calculate relevance score for search results."""

	def __init__(self, rules: tuple, weights: RelevanceWeights) -> None:
		self.rules = rules
		self.w = weights
		self.mod_time_half_life = max(1.0, weights.half_life) * 86400.0
		logger.debug(f"RelevanceScorer initialized with {len(rules)} rules, weights: {weights._asdict()}")

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode = get_raw_stat(path)
		if not is_dir and size == 0:
			return 0.0

		score = 0.0
		if self.rules:
			for patterns, action in self.rules:
				if any(fnmatch(path_lower, p) for p in patterns):
					score += action

		score -= min(path.count("/"), 12) * self.w.depth
		name_lower = os.path.basename(path_lower)
		n = max(1, len(name_lower))
		if matches := [
			1.75 * 2.7183 ** (-0.8 * (i / n)) * ((len(w) / n) ** 0.7) for w in words if 1 + (i := name_lower.find(w))
		]:
			score += max(matches) + (m := len(matches)) * 0.7 / (m + 2.5)

		if is_dir:
			score += self.w.dir_bonus
		else:
			if mode & 0o111:
				score += self.w.exec_bonus

			if mtime and mtime <= now:
				logit = max(0.0, now - mtime) / self.mod_time_half_life
				if logit < 7:
					score += self.w.mod_time if logit <= 0.001 else self.w.mod_time * 2.7183 ** (-logit)

		if score <= -7:
			return 0.0

		if score >= 7:
			return 1.0

		return 1.0 / (1.0 + 2.7183 ** (-score))


class Runner(dbus.service.Object):
	"""Main D-Bus service for integration with KRunner."""

	cache_dir = os.path.dirname(CACHE_FILE)

	def __init__(self) -> None:
		super().__init__(dbus.service.BusName(DBUS_BUSNAME, dbus.SessionBus()), "/runner")
		self.cfg = _GLOBAL_CFG
		found = _find_command(get_config_value(self.cfg, "binary", "plocate"), "locate")
		if found:
			self.binary = found[0]
			logger.info(f"Using search binary: {self.binary}")
		else:
			msg = f"{PROG_NAME.capitalize()} cannot function without 'plocate' or 'locate' installed."
			raise RuntimeError(msg)

		opts = self.cfg.get("opts", "-i")
		self.opts = tuple(normalize_shlex(opts))
		if not any(x in self.opts for x in ("-l", "--limit")):
			self.opts += ("-l", "200")

		logger.debug(f"Search options: {self.opts}")
		self.opener = get_command_list(self.cfg, "opener", [["handlr", "open"], "mimeo", "xdg-open"])
		self.clipboard_cmd_text = get_command_list(self.cfg, "clipboard_cmd_text", [])
		self.clipboard_cmd_uri = get_command_list(self.cfg, "clipboard_cmd_uri", [])
		logger.debug(
			f"Clipboard commands - text: {self.clipboard_cmd_text or 'auto-detect'}, "
			f"uri: {self.clipboard_cmd_uri or 'auto-detect'}"
		)
		self.min_len = max(1, get_config_value(self.cfg, "min_len", 2, int))
		self.debounce_ms = get_config_value(self.cfg, "debounce_ms", 180, int)
		self.locate_timeout = get_config_value(self.cfg, "locate_timeout", 5.0, float)
		self.max_cached = get_config_value(self.cfg, "history_size", 800, int)
		self.expiry_dates = get_config_value(self.cfg, "expiry_dates", 3.0, float)
		logger.info(
			f"Runner initialized - binary: {self.binary}, min_len: {self.min_len}, "
			f"debounce: {self.debounce_ms}ms, timeout: {self.locate_timeout}s"
		)
		weights = RelevanceWeights(
			half_life=get_config_value(self.cfg, "mod_time_half_life_days", 30.0, float),
			mod_time=get_config_value(self.cfg, "mod_time_weight", 0.60, float),
			depth=get_config_value(self.cfg, "depth_penalty", 0.015, float),
			exec_bonus=get_config_value(self.cfg, "executable_bonus", 0.18, float),
			dir_bonus=get_config_value(self.cfg, "directory_bonus", 0.35, float),
		)
		self.scorer = RelevanceScorer(self._parse_rules(), weights)
		self.search_results = self._load_cache()
		self._current_query_norm: str | None = None
		self._query_lock = Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer = None

	def _parse_rules(self) -> tuple:
		rules = []
		for item in self.cfg.get("rules", []):
			if not isinstance(item, dict):
				continue

			p = item.get("patterns")
			s = item.get("score")
			if p is None or s is None:
				logger.warning(f"Invalid rule (missing patterns or score): {item}")
				continue

			pat = normalize_list(p)
			try:
				rules.append((tuple(intern(x.strip().lower()) for x in pat), float(s)))
			except (ValueError, TypeError) as e:
				logger.warning(f"Invalid rule format: {item} - {e}")
				continue

		logger.info(f"Parsed {len(rules)} scoring rules from configuration")
		return tuple(rules)

	def _load_cache(self) -> OrderedDict:
		try:
			_verify_dir_access(self.cache_dir)
			fd = _verify_file_access(CACHE_FILE)
			start_t = time()
			with os.fdopen(fd, "rb") as f:
				raw = json.loads(zlib.decompress(f.read()))

			validated = OrderedDict()
			now = time()
			for k, v in raw.items():
				match v:
					case [ts, result_list] if (
						isinstance(k, str) and isinstance(ts, (int, float)) and isinstance(result_list, list)
					):
						if now - ts > self.expiry_dates * 86400:
							continue

						items = []
						for res in result_list:
							match res:
								case [str(p), str(i), str(t), s] if isinstance(s, (int, float)):
									items.append(LightResult(p, i, t, float(s)))

						if items:
							validated[k] = (ts, tuple(items))

			entries_removed = max(0, len(validated) - self.max_cached)
			if entries_removed > 0:
				logger.debug(f"Trimming cache: removing {entries_removed} oldest entries")
				while len(validated) > self.max_cached:
					validated.popitem(last=False)

			logger.info(f"Cache loaded in {time() - start_t:.3f}s with {len(validated)} entries")
			return validated
		except FileNotFoundError:
			logger.info("No cache file found, starting with empty cache")
			return OrderedDict()
		except PermissionError:
			logger.exception("Cache permission error")
			return OrderedDict()
		except (json.JSONDecodeError, zlib.error):
			logger.exception("Cache file corrupted")
			return OrderedDict()
		except (OSError, ValueError):
			logger.exception("Failed to load cache")
			return OrderedDict()

	def save_cache(self) -> None:
		try:
			serializable = {
				k: [ts, [(r.path, r.icon, r.subtext, r.score) for r in res]]
				for k, (ts, res) in self.search_results.items()
			}
			try:
				_verify_dir_access(self.cache_dir)
			except FileNotFoundError:
				logger.info(f"Creating cache directory: {self.cache_dir}")
				os.makedirs(self.cache_dir, mode=0o700)

			fd = _verify_file_write(CACHE_FILE)
			with os.fdopen(fd, "wb") as f:
				compressed = zlib.compress(json.dumps(serializable, ensure_ascii=False).encode("utf-8"), level=6)
				f.write(compressed)

			logger.info(
				f"Cache saved successfully with {len(self.search_results)} entries ({len(compressed)} bytes compressed)"
			)
		except PermissionError:
			logger.exception(f"Cache save permission error for '{CACHE_FILE}' or '{self.cache_dir}'")
		except (OSError, ValueError):
			logger.exception(f"Cache save failed to '{CACHE_FILE}'")

	def _is_query_stale(self, query: str) -> bool:
		with self._query_lock:
			return self._current_query_norm != query

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		if self._is_query_stale(norm_query) or not self.binary:
			return

		logger.debug(f"Starting search for query: '{norm_query}' (words: {words})")
		proc = None
		discarded_by_score = 0
		try:
			proc = subprocess.Popen(
				[self.binary, *self.opts, *words],
				stdout=subprocess.PIPE,
				stderr=subprocess.DEVNULL,
				bufsize=IO_CHUNK_SIZE,
				start_new_session=True,
			)
			fd = proc.stdout.fileno()
			os.set_blocking(fd, False)
			top_k_heap, now, paths_seen = [], time(), 0
			read_buffer = b""
			start_time = now
			while True:
				if self._is_query_stale(norm_query):
					logger.debug(f"Query became stale, aborting search: '{norm_query}'")
					break

				elapsed = time() - start_time
				if elapsed > self.locate_timeout:
					logger.warning(f"Search timeout after {elapsed:.2f}s for query: '{norm_query}'")
					break

				ready, _, _ = select([fd], [], [], 0.05)
				if fd in ready:
					chunk = proc.stdout.read(IO_CHUNK_SIZE)
					if not chunk:
						break

					read_buffer += chunk
					while b"\n" in read_buffer:
						line_bytes, read_buffer = read_buffer.split(b"\n", 1)
						if not (path := validate_str(line_bytes)):
							continue

						paths_seen += 1
						if paths_seen > MAX_TOTAL_RESULTS * 3:
							logger.debug(f"Hit path limit ({MAX_TOTAL_RESULTS * 3}), stopping scan")
							read_buffer = b""
							break

						score = self.scorer.calculate(path, path.lower(), words, now)
						if score <= 0.01:
							discarded_by_score += 1
							continue

						entry = (score, path)
						if len(top_k_heap) < MAX_TOTAL_RESULTS:
							heappush(top_k_heap, entry)
						elif score > top_k_heap[0][0]:
							heappushpop(top_k_heap, entry)

					if paths_seen > MAX_TOTAL_RESULTS * 3:
						break
				elif proc.poll() is not None:
					break
		except (OSError, ValueError, subprocess.SubprocessError) as e:
			logger.warning(f"Search subprocess error for query '{norm_query}': {e.__class__.__name__}")
			logger.debug(f"Search command was: {[self.binary, *self.opts, *words]}")
		finally:
			if proc:
				with suppress(Exception):
					if proc.poll() is None:
						proc.terminate()
						try:
							proc.wait(timeout=1.0)
						except subprocess.TimeoutExpired:
							logger.warning(f"Search process did not terminate, killing: '{norm_query}'")
							proc.kill()
							with suppress(subprocess.TimeoutExpired):
								proc.wait(timeout=2.0)

					if proc.stdout:
						proc.stdout.close()

		if not self._is_query_stale(norm_query):
			elapsed = time() - start_time
			final = sorted(top_k_heap, reverse=True)
			if not final and paths_seen == 0:
				logger.warning(f"No results for '{norm_query}'. Is the locate database empty?")

			results = tuple(LightResult(p, *get_icon_and_subtext(p), s) for s, p in final)
			logger.info(
				f"Search completed: '{norm_query}' | Scanned: {paths_seen} | Kept: {len(results)} | "
				f"Rejected: {discarded_by_score} | Time: {elapsed:.2f}s"
			)
			GLib.idle_add(self._on_search_finished, norm_query, results)
		else:
			logger.debug(f"Discarding results for stale query: '{norm_query}'")

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...]) -> bool:
		if not self._is_query_stale(query):
			now = time()
			self.search_results[query] = (now, results)
			if len(self.search_results) > self.max_cached:
				self.search_results.popitem(last=False)

			logger.debug(f"Cached {len(results)} results for query: '{query}'")

		return False

	@dbus.service.method(IFACE_KRUNNER, in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str) -> list:
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []

		try:
			words = tuple(w.lower() for w in shlex_split(stripped))
			norm = " ".join(words)
		except (ValueError, AttributeError):
			norm = " ".join(words := tuple(stripped.lower().split()))

		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)

		with self._query_lock:
			self._current_query_norm = norm

		if norm in self.search_results:
			_, res = self.search_results[norm]
			self.search_results.move_to_end(norm)
			logger.info(f"Cache hit for query: '{norm}' ({len(res)} results)")
			return build_dbus_response(list(res))

		logger.debug(f"New query received: '{norm}' (debounce: {self.debounce_ms}ms)")
		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)
		for key, value in reversed(self.search_results.items()):
			_, res = value
			is_safe_prefix = norm.startswith(key) and len(key) >= max(2, len(norm) - 6)
			if is_safe_prefix and len(res) < MAX_TOTAL_RESULTS:
				filtered = [r for r in res if all(w in r.path.lower() for w in words)]
				logger.debug(f"Using prefix match from '{key}': {len(filtered)} results")
				return build_dbus_response(filtered)

		return []

	def _debounce_callback(self, norm: str, words: tuple) -> bool:
		self._debounce_timer = None
		logger.info(f"Debounce expired ({self.debounce_ms}ms), submitting search job: '{norm}'")
		self.executor.submit(self._run_locate_job, norm, words)
		return False

	@dbus.service.method(IFACE_KRUNNER, out_signature="a(sss)")
	def Actions(self) -> list:
		return [
			("open", "Open File", "document-open"),
			("parent", "Open Parent Folder", "inode-directory"),
			("copy", "Copy Path", "edit-copy"),
			("copy-uri", "Copy File (Paste Ready)", "edit-copy-path"),
		]

	@dbus.service.method(IFACE_KRUNNER, in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		try:
			safe_path = validate_str(os.path.realpath(data))
		except (OSError, ValueError):
			logger.warning(f"Failed to resolve path '{data}'")
			return

		if not safe_path:
			logger.warning(
				f"Invalid path received in Run action '{action_id}': {data!r} (contains null bytes or decode error)"
			)
			return

		action = action_id or "open"
		logger.debug(f"Executing action '{action}' on path: {safe_path}")

		match action:
			case "open" if self.opener:
				_spawn([*self.opener, safe_path])

			case "parent" if self.opener:
				parent_dir = os.path.dirname(safe_path)
				logger.debug(f"Opening parent directory: {parent_dir}")
				_spawn([*self.opener, parent_dir])

			case "copy":
				success = self._exec_clipboard(safe_path, MIME_TEXT, self.clipboard_cmd_text)
				logger.debug(f"Copy path to clipboard: {'success' if success else 'failed'}")

			case "copy-uri":
				uri = "file://" + quote_from_bytes(os.fsencode(safe_path)) + "\r\n"
				success = self._exec_clipboard(uri, MIME_URI, self.clipboard_cmd_uri)
				logger.debug(f"Copy URI to clipboard: {'success' if success else 'failed'}")

			case _:
				logger.warning(f"Unknown action requested: '{action}'")

	def _exec_clipboard(self, data: str, mime: str, configured_cmd: list[str]) -> bool:
		"""Copy data to clipboard using configured command or fallbacks."""
		if not validate_str(data):
			logger.warning(f"Invalid data for clipboard operation (mime: {mime})")
			return False

		truncated_data = data[:8192]
		if len(data) > 8192:
			logger.debug(f"Clipboard data truncated from {len(data)} to 8192 bytes")

		if configured_cmd and _run_subprocess_input(configured_cmd, truncated_data):
			logger.debug(f"Clipboard operation succeeded using configured command: {configured_cmd[0]}")
			return True

		for cmd in CLIPBOARD_PROVIDERS.get(mime, []):
			if which(cmd[0]) and _run_subprocess_input(list(cmd), truncated_data):
				logger.debug(f"Clipboard operation succeeded using fallback: {cmd[0]}")
				return True

		logger.warning(f"All clipboard operations failed for mime type: {mime}")
		available_providers = [cmd[0] for cmd in CLIPBOARD_PROVIDERS.get(mime, []) if which(cmd[0])]
		logger.debug(f"Available clipboard providers for {mime}: {available_providers or 'none'}")
		return False


# ========== MAIN ==========
if __name__ == "__main__":
	logger.info(f"Starting {PROG_NAME.capitalize()}'s main loop")
	try:
		DBusGMainLoop(set_as_default=True)
		runner = Runner()
		logger.notice(f"{PROG_NAME.capitalize()} registered on DBus: {DBUS_BUSNAME}")
		loop = GLib.MainLoop()

		def quit_handler(signum: int, *_: Any) -> None:
			sig_name = signal.Signals(signum).name if hasattr(signal, 'Signals') else str(signum)
			logger.notice(f"Received {sig_name}, shutting down gracefully")
			runner.save_cache()
			loop.quit()

		signal(SIGINT, quit_handler)
		signal(SIGTERM, quit_handler)
		logger.info("Entering main loop")
		loop.run()
	except KeyboardInterrupt:
		logger.info("Keyboard interrupt received")
		runner.save_cache()
	except Exception:
		logger.critical("Fatal error in main loop", exc_info=True)
		raise
	finally:
		logger.notice(f"{PROG_NAME.capitalize()} stopped")
else:
	logger.warning(f"{PROG_NAME.capitalize()} was not started directly, stopping")
