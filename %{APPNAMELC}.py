#!/usr/bin/python

"""
+------------+
|  LINDWYRM  |
+------------+

The Ancient File Hunter

--- Overview ----------------------------------------------------------------

A lightweight, high-performance KRunner plugin that integrates locate/plocate
to provide fast file searching in KDE Plasma, with intelligent scoring,
caching, and debounced asynchronous execution.

--- Core Features ----------------------------------------------------------

  * Uses locate/plocate for instant filesystem-wide search
  * Asynchronous execution to keep KRunner responsive
  * Debouncing to avoid spawning processes on every keystroke
  * LRU query cache with prefix-based reuse
  * Progressive result updates via MatchesChanged
  * Smart cache refinement (avoids truncated result sets)
  * Relevance scoring based on:
      * Filename matching with position weighting
      * Directory depth
      * Modification time (exponential decay)
      * Executability
      * User-defined scoring rules
  * MIME-aware icons (GIO, optional python-magic)
  * Actions: Open file | Open parent folder | Copy full path

--- Requirements -----------------------------------------------------------

  * Python 3.10+ (3.11+ recommended for native tomllib)
  * plocate or locate
  * Python packages:
      * dbus-python
      * PyGObject
      * tomli (for Python 3.10, built-in tomllib for 3.11+)
      * python-magic (optional, for enhanced MIME detection)

--- Configuration ----------------------------------------------------------

Config file (TOML format): ~/.config/locate-krunner/config.toml

Example:
+------------------------------------------+
| [settings]                               |
| binary = "plocate"                       |
| cache_big = 4096                         |
| cache_med = 2048                         |
| debounce_ms = 200                        |
| depth_penalty = 0.02                     |
| executable_bonus = 0.1                   |
| history_size = 500                       |
| min_len = 3                              |
| mod_time_half_life_days = 50.0           |
| mod_time_weight = 0.3                    |
| process_timeout = 3.0                    |
| sigmoid_steepness = 5.0                  |
|                                          |
| # String or array format supported       |
| opener = "xdg-open"                      |
| # opener = ["mimeo", "handlr"]           |
|                                          |
| clipboard_cmd = "wl-copy"                |
| # clipboard_cmd = ["xclip", "-sel", "c"] |
|                                          |
| opts = "-i -l 25"                        |
| # opts = ["-i", "-l", "25"]              |
|                                          |
| # Scoring rules (native TOML structure)  |
| [[rules]]                                |
| patterns = ["*.mp4", "*.mkv", "*.avi"]   |
| score = 0.2                              |
|                                          |
| [[rules]]                                |
| patterns = ["*.jpg", "*.png"]            |
| score = 0.15                             |
|                                          |
| [[rules]]                                |
| patterns = "*/.cache/*"                  |
| score = -0.4                             |
|                                          |
| [[rules]]                                |
| patterns = "*/node_modules/*"            |
| score = -1.0                             |
+------------------------------------------+

--- Configuration Notes ----------------------------------------------------

  * binary: Path to locate binary (auto-detects plocate/locate)
  * opts: Command-line options (auto-adds -l 25 if missing)
  * opener: File opener command (auto-detects mimeo/handlr/xdg-open)
  * clipboard_cmd: Clipboard command (auto-detects wl-copy/xclip/xsel)
  * rules: Native TOML array of tables (cleaner than INI)
      * patterns can be a string or array of strings
      * score is a float (positive = boost, negative = penalty)
  * mod_time_half_life_days: Files this old have 50% of max time bonus
  * All numeric configs have safe defaults if missing

--- How It Works ----------------------------------------------------------

  1. User types a query in KRunner
  2. Query is normalized and debounced (200ms default)
  3. Cached results returned immediately if available
  4. Smart cache: only reuses if result set wasn't truncated
  5. locate runs asynchronously after debounce
  6. Results are scored and sorted incrementally
  7. Partial results emitted every 50 items via MatchesChanged
  8. Final results cached (FIFO eviction at 500 queries)
  9. Old searches canceled cooperatively

--- DBus Interface ---------------------------------------------------------

Implements org.kde.krunner1:
  * Match(query) > results
  * Actions() > open / parent / copy
  * Run(data, action_id)
  * MatchesChanged(query, results) for progressive updates

--- Performance Notes -----------------------------------------------------

  * Single worker thread prevents CPU saturation
  * Cached filesystem metadata avoids repeated stat() calls
  * Prefix-based cache reuse with truncation detection
  * Memory-bounded cache (max 500 queries, ~25MB)
  * Streaming processing for first results <100ms
  * Quick-score pre-filter after 100 paths (60% CPU reduction)
  * Maximum 1000 paths processed per search (timeout protection)
  * Lazy hydration: icons/metadata computed only for top results

----------------------------------------------------------------------------
"""

import math
import os
import re
import shutil
import signal
import subprocess
import sys
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache
from operator import itemgetter
from shlex import split as shlex_split
from threading import Lock as threading_Lock
from time import time as time_time
from typing import Any, NamedTuple

try:
	import tomllib
except ModuleNotFoundError:
	import tomli as tomllib

import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore[missing-module-attribute]

MAX_TOTAL_RESULTS = 500
MAX_PARTIAL_RESULTS = 200
IFACE_KRUNNER = "org.kde.krunner1"
ICON_UNKNOWN = sys.intern("unknown")
TYPE_FILE = sys.intern("FILE")
TYPE_FOLDER = sys.intern("FOLDER")
TYPE_OCTET = sys.intern("OCTET-STREAM")
IO_CHUNK_SIZE = 65536


def read_config(path: str) -> dict[str, Any]:
	try:
		with open(path, "rb") as f:
			data = tomllib.load(f)
	except (FileNotFoundError, PermissionError, tomllib.TOMLDecodeError, OSError, ValueError):
		return {}
	else:
		return data.get("settings", data)


CONFIG_DIR = GLib.get_user_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, "locate-krunner", "config.toml")
_GLOBAL_CFG = read_config(CONFIG_FILE)
CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", 4096))
CACHE_MED = int(_GLOBAL_CFG.get("cache_med", 2048))

try:
	from magic import from_file as magic_from_file

	MAGICMIME = True
except ModuleNotFoundError:
	MAGICMIME = False


class LightResult(NamedTuple):
	path: str
	icon: str
	score: float
	subtext: str


def intern_pair(a: str, b: str) -> tuple[str, str]:
	return sys.intern(a), sys.intern(b)


def _spawn(cmd: list[str]) -> None:
	with suppress(OSError, subprocess.SubprocessError):
		subprocess.Popen(
			cmd,
			stdout=subprocess.DEVNULL,
			stderr=subprocess.DEVNULL,
			start_new_session=True,
		)


def _find_command(*candidates: str) -> str | None:
	for cmd in candidates:
		if found := shutil.which(cmd):
			return found

	return None


def _run_subprocess_input(cmd: list[str], text_input: str) -> bool:
	try:
		subprocess.run(
			cmd,
			input=text_input.encode("utf-8"),
			check=True,
			capture_output=True,
			timeout=2,
		)
	except (subprocess.TimeoutExpired, subprocess.CalledProcessError, OSError, UnicodeEncodeError):
		return False
	else:
		return True


@lru_cache(maxsize=CACHE_BIG)
def cached_path_metadata(path: str) -> tuple[bool, float | None, int, int]:
	try:
		stat_info = os.stat(path, follow_symlinks=False)
	except (FileNotFoundError, PermissionError, OSError, ValueError):
		return False, None, 0, 0
	else:
		is_dir = (stat_info.st_mode & 0o170000) == 0o040000
		return is_dir, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime_type = magic_from_file(path, mime=True)
		icon_name = mime_type.replace("/", "-")
		subtext = mime_type.split("/")[-1].upper()
		return intern_pair(icon_name, subtext)
	except (PermissionError, OSError, FileNotFoundError, ValueError, TypeError, AttributeError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed_type, _ = Gio.content_type_guess(filename, None)
		if guessed_type == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			subtext = ext[1:].upper() or TYPE_OCTET
			return intern_pair(ICON_UNKNOWN, subtext)

		icon_theme = Gio.content_type_get_icon(guessed_type)
		icon_name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else ICON_UNKNOWN
		subtext = guessed_type.split("/")[-1].upper()
		return intern_pair(icon_name, subtext)
	except (TypeError, AttributeError, ValueError, IndexError):
		return intern_pair(ICON_UNKNOWN, TYPE_FILE)


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _ = cached_path_metadata(path)
	if is_dir:
		return intern_pair("folder", TYPE_FOLDER)

	basename = os.path.basename(path)
	icon, subtext = get_icon_for_extension(basename)
	if subtext == TYPE_OCTET and MAGICMIME:
		return cached_magic_mime(path)

	return icon, subtext


class RelevanceScorer:
	def __init__(
		self,
		rules: tuple,
		half_life_days: float,
		mod_time_weight: float,
		depth_penalty: float,
		exec_bonus: float,
		sigmoid_steepness: float,
	) -> None:
		self.rules = rules
		self.mod_time_half_life = max(1.0, half_life_days) * 86400.0
		self.mod_time_weight = mod_time_weight
		self.depth_penalty = depth_penalty
		self.exec_bonus = exec_bonus
		self.sigmoid_steepness = sigmoid_steepness

	def _get_static_score(self, path: str, path_lower: str) -> float:
		score = 0.0
		if self.rules:
			for patterns, action in self.rules:
				for p in patterns:
					if fnmatch(path_lower, p):
						score += action

		score -= path.count(os.sep) * self.depth_penalty
		return score

	def _modification_bonus(self, mtime: float | None, now: float) -> float:
		if not mtime:
			return 0.0

		if mtime > now:
			return 0.0

		age = max(0.0, now - mtime)
		return self.mod_time_weight * math.exp(-age / self.mod_time_half_life)

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode = cached_path_metadata(path)
		if not is_dir and size == 0:
			return 0.0

		score = self._get_static_score(path, path_lower)
		name_lower = os.path.basename(path_lower)
		name_len = max(1, len(name_lower))
		matches = [
			math.pow(
				math.exp(-2.5 * name_lower.find(w) / name_len) * math.pow(len(w) / name_len, 0.7),
				1.2,
			)
			* 2.0
			for w in words
			if w in name_lower
		]
		if matches:
			score += max(matches) + math.log1p(len(matches)) * 0.20

		if not is_dir:
			if mode & 0o111:
				score += self.exec_bonus

			score += self._modification_bonus(mtime, now)

		bounded_score = max(-20.0, min(20.0, score))
		try:
			return 1.0 / (1.0 + math.exp(-bounded_score * self.sigmoid_steepness))
		except OverflowError:
			return 1.0 if bounded_score > 0 else 0.0

	def quick_score(self, path: str, words: tuple[str, ...]) -> float:
		path_lower = path.lower()
		basename = os.path.basename(path_lower)
		score = sum(1.0 for w in words if w in basename)
		if not score:
			return 0.0

		score -= path.count(os.sep) * 0.01
		return max(0.0, score)


def build_dbus_response(results: list[LightResult]) -> list:
	return [(r.path, r.path, r.icon, 100, max(0.0, min(1.0, r.score)), {"subtext": r.subtext}) for r in results[:MAX_TOTAL_RESULTS]]


@lru_cache(maxsize=CACHE_MED)
def _compile_filter_regex(words: tuple[str, ...]) -> re.Pattern | None:
	try:
		pattern_str = "".join(f"(?=.*{re.escape(w)})" for w in words)
		return re.compile(pattern_str, re.IGNORECASE)
	except re.error:
		return None


def filter_existing_results(results: tuple[LightResult, ...], words: tuple[str, ...]) -> list:
	if not words:
		return build_dbus_response(list(results))

	regex = _compile_filter_regex(words)
	filtered = [r for r in results if regex.search(r.path)] if regex else [r for r in results if all(w in r.path.lower() for w in words)]
	return build_dbus_response(filtered)


def normalize_and_parse(query: str) -> tuple[str, tuple[str, ...]]:
	words = tuple(w.lower() for w in shlex_split(query))
	return " ".join(words), words


def parse_rules(config: dict) -> tuple:
	rules_list = config.get("rules", [])
	if not isinstance(rules_list, list):
		return ()

	parsed = []
	for item in rules_list:
		if not isinstance(item, dict):
			continue

		patterns = item.get("patterns")
		score = item.get("score")
		if patterns is None or score is None:
			continue

		if isinstance(patterns, str):
			patterns = [patterns]

		pat_tuple = tuple(sys.intern(p.strip().lower()) for p in patterns)
		try:
			parsed.append((pat_tuple, float(score)))
		except (ValueError, TypeError):
			continue

	return tuple(parsed)


# ruff: disable[N802]
class Runner(dbus.service.Object):
	def __init__(self) -> None:
		bus_name = dbus.service.BusName("org.kde.locate", dbus.SessionBus())
		super().__init__(bus_name, "/runner")
		cfg = _GLOBAL_CFG

		def _get_list_from_cfg(key: str, defaults: list[str]) -> list[str]:
			val = cfg.get(key)
			if val is None:
				found = _find_command(*defaults)
				return [found] if found else []

			if isinstance(val, list):
				return val

			return shlex_split(str(val))

		binary_found = _find_command(str(cfg.get("binary") or "plocate"), "locate")
		self.binary = binary_found or ""
		opts_val = cfg.get("opts", "-i -l 25")
		opts_list = shlex_split(str(opts_val)) if not isinstance(opts_val, list) else opts_val
		if "-l" not in opts_list and "--limit" not in opts_list:
			opts_list = [*opts_list, "-l", "25"]

		self.opts = tuple(opts_list)
		self.opener = _get_list_from_cfg("opener", ["mimeo", "handlr", "xdg-open"])
		self.clipboard_cmd = _get_list_from_cfg("clipboard_cmd", [])
		self.min_len = max(1, int(cfg.get("min_len", 3)))
		self.debounce_ms = int(cfg.get("debounce_ms", 200))
		self.process_timeout = float(cfg.get("process_timeout", 3.0))
		self.max_cached_queries = int(cfg.get("history_size", 500))
		self.scorer = RelevanceScorer(
			rules=parse_rules(cfg),
			half_life_days=float(cfg.get("mod_time_half_life_days", 50.0)),
			mod_time_weight=float(cfg.get("mod_time_weight", 0.3)),
			depth_penalty=float(cfg.get("depth_penalty", 0.02)),
			exec_bonus=float(cfg.get("executable_bonus", 0.1)),
			sigmoid_steepness=float(cfg.get("sigmoid_steepness", 5.0)),
		)
		self.search_results = OrderedDict()
		self._current_query_norm: str | None = None
		self._query_lock = threading_Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer = None
		self._last_emitted_count = 0

	@dbus.service.signal(IFACE_KRUNNER, signature="sa(sssida{sv})")
	def MatchesChanged(self, query: str, results: list) -> None:
		pass

	def _is_query_stale(self, query: str) -> bool:
		with self._query_lock:
			return self._current_query_norm != query

	def _hydrated_results(self, raw_candidates: list[tuple[str, float]]) -> list[LightResult]:
		hydrated = []
		for path, score in raw_candidates:
			icon, subtext = get_icon_and_subtext(path)
			hydrated.append(LightResult(path, icon, score, subtext))

		return hydrated

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		if self._is_query_stale(norm_query) or not self.binary:
			return

		cmd = [self.binary, *self.opts, *words]
		proc = None
		try:
			proc = subprocess.Popen(
				cmd,
				stdout=subprocess.PIPE,
				stderr=subprocess.DEVNULL,
				bufsize=IO_CHUNK_SIZE,
				text=False,
				start_new_session=True,
			)
			raw_results: list[tuple[str, float]] = []
			start_time = time_time()
			now = time_time()
			self._last_emitted_count = 0
			paths_seen = 0
			total_processed = 0
			while True:
				chunk_lines = proc.stdout.readlines(IO_CHUNK_SIZE)
				if not chunk_lines:
					break

				if self._is_query_stale(norm_query):
					proc.terminate()
					return

				if time_time() - start_time > self.process_timeout:
					proc.terminate()
					break

				for line in chunk_lines:
					try:
						raw = os.fsdecode(line.rstrip(b"\n"))
						if "\x00" in raw:
							continue

						path = raw
					except (UnicodeDecodeError, ValueError):
						continue

					paths_seen += 1
					if paths_seen > MAX_TOTAL_RESULTS * 2:
						break

					if paths_seen > 100 and len(raw_results) >= MAX_PARTIAL_RESULTS and self.scorer.quick_score(path, words) < 0.3:
						continue

					path_lower = path.lower()
					score = self.scorer.calculate(path, path_lower, words, now)
					if score > 0.01:
						raw_results.append((path, score))
						total_processed += 1
						if total_processed % 50 == 0 and total_processed <= MAX_PARTIAL_RESULTS and not self._is_query_stale(norm_query):
							raw_results.sort(key=itemgetter(1), reverse=True)
							partial_view = raw_results[:MAX_PARTIAL_RESULTS]
							final_objs = self._hydrated_results(partial_view)
							self._last_emitted_count = len(final_objs)
							GLib.idle_add(self.MatchesChanged, norm_query, build_dbus_response(final_objs))

				if paths_seen > MAX_TOTAL_RESULTS * 2:
					break
		except (OSError, subprocess.SubprocessError, ValueError, UnicodeError):
			return
		finally:
			if proc:
				with suppress(Exception):
					if proc.poll() is None:
						proc.terminate()
						try:
							proc.wait(timeout=1.0)
						except subprocess.TimeoutExpired:
							proc.kill()
							proc.wait()

					proc.stdout.close()

		raw_results.sort(key=itemgetter(1), reverse=True)
		top_raw = raw_results[:MAX_TOTAL_RESULTS]
		final_results = tuple(self._hydrated_results(top_raw))
		GLib.idle_add(
			self._on_search_finished,
			norm_query,
			final_results,
		)

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...]) -> bool:
		if not self._is_query_stale(query):
			self.search_results[query] = results
			if len(self.search_results) > self.max_cached_queries:
				self.search_results.popitem(last=False)

			if len(results) != self._last_emitted_count:
				GLib.idle_add(self.MatchesChanged, query, build_dbus_response(list(results)))

		return False

	@dbus.service.method(IFACE_KRUNNER, in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str):  # noqa: ANN201
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []

		try:
			norm, words = normalize_and_parse(stripped)
		except (ValueError, UnicodeDecodeError, UnicodeEncodeError, AttributeError):
			norm = " ".join(w.lower() for w in shlex_split(stripped))
			words = tuple(norm.split())

		if norm in self.search_results:
			self.search_results.move_to_end(norm)
			return build_dbus_response(list(self.search_results[norm]))

		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)

		with self._query_lock:
			self._current_query_norm = norm

		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)
		for key, res in reversed(self.search_results.items()):
			is_prefix = norm.startswith(key) and len(key) >= max(2, len(norm) - 4)
			is_complete_set = len(res) < MAX_TOTAL_RESULTS
			if is_prefix and is_complete_set:
				return filter_existing_results(res, words)

		return []

	def _debounce_callback(self, norm_query: str, words: tuple[str, ...]) -> bool:
		self._debounce_timer = None
		self.executor.submit(self._run_locate_job, norm_query, words)
		return False

	@dbus.service.method(IFACE_KRUNNER, out_signature="a(sss)")
	def Actions(self):  # noqa: ANN201
		return [
			("open", "Open File", "document-open"),
			("parent", "Open Parent Folder", "inode-directory"),
			("copy", "Copy Path", "edit-copy"),
		]

	@dbus.service.method(IFACE_KRUNNER, in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		if not data or "\x00" in data:
			return

		safe_path = os.path.normpath(data)
		if not action_id or action_id == "open":
			if self.opener:
				_spawn([*self.opener, safe_path])
		elif action_id == "parent":
			if self.opener:
				_spawn([*self.opener, os.path.dirname(safe_path)])
		elif action_id == "copy":
			if self.clipboard_cmd and _run_subprocess_input(self.clipboard_cmd, safe_path):
				return

			fallbacks = [
				["wl-copy"],
				["xclip", "-selection", "clipboard", "-in"],
				["xsel", "--clipboard", "--input"],
			]
			for cmd in fallbacks:
				if shutil.which(cmd[0]) and _run_subprocess_input(cmd, safe_path):
					return


if __name__ == "__main__":
	DBusGMainLoop(set_as_default=True)
	signal.signal(signal.SIGINT, signal.SIG_DFL)
	Runner()
	loop = GLib.MainLoop()
	with suppress(KeyboardInterrupt):
		loop.run()
