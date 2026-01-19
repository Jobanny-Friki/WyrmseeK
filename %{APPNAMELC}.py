#!/usr/bin/python
# flake8: noqa: PLR2004

"""
## KRunner Locate Plugin

### Overview

A lightweight, high-performance KRunner plugin that integrates `locate` / `plocate` to provide fast file
searching in KDE Plasma, with intelligent scoring, caching, and debounced asynchronous execution.

### Core Features

* Uses **locate / plocate** for instant filesystem-wide search
* **Asynchronous execution** to keep KRunner responsive
* **Debouncing** to avoid spawning processes on every keystroke
* **LRU query cache** with prefix-based reuse
* **Progressive result updates** via `MatchesChanged`
* **Relevance scoring** based on:

  * filename matching
  * directory depth
  * modification time
  * executability
  * user-defined scoring rules
* **MIME-aware icons** (GIO, optional `python-magic`)
* Actions:

  * Open file
  * Open parent folder
  * Copy full path to clipboard

---

### Requirements

* Python **3.10+**
* `plocate` or `locate`
* Python packages:

  * `dbus-python`
  * `PyGObject`
  * `python-magic` (optional)

---

### Configuration

Config file:

```
~/.config/locate-krunner/config.ini
```

Example:

```ini
[Settings]
binary = plocate
opts = -i -l 25
opener = handlr open
clipboard_cmd = wl-copy
min_len = 3
debounce_ms = 200
process_timeout = 3.0
history_size = 500

cache_big = 4096
cache_med = 2048

mod_time_half_life_days = 50
mod_time_weight = 0.3
depth_penalty = 0.02
executable_bonus = 0.1
sigmoid_steepness = 5.0

scoring_rule_1 = */documents/*:0.5
scoring_rule_2 = */node_modules/*:-1.0
```

---

### How It Works (High Level)

1. User types a query in KRunner
2. Query is normalized and debounced
3. Cached results are returned immediately if available
4. `locate` runs asynchronously after debounce
5. Results are scored and sorted incrementally
6. Partial results are emitted via `MatchesChanged`
7. Final results are cached and returned

---

### DBus Interface

Implements `org.kde.krunner1`:

* `Match(query)` → results
* `Actions()` → open / parent / copy
* `Run(data, action_id)`
* `MatchesChanged(query, results)` for live updates

---

### Performance Notes

* Single worker thread prevents CPU saturation
* Cached filesystem metadata avoids repeated `stat()` calls
* Prefix-based cache reuse enables instant refinement
* Old searches are canceled cooperatively
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
from configparser import ConfigParser
from contextlib import suppress
from fnmatch import fnmatch
from functools import lru_cache
from operator import attrgetter
from shlex import split as shlex_split
from time import time as time_time
from threading import Lock as threading_Lock
from typing import NamedTuple
import dbus.service
from dbus.mainloop.glib import DBusGMainLoop
from gi.repository import Gio, GLib  # type: ignore[missing-module-attribute]

try:
	from magic import from_file as magic_from_file

	MAGICMIME = True
except ModuleNotFoundError:
	MAGICMIME = False

DBusGMainLoop(set_as_default=True)
CONFIG_DIR = GLib.get_user_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, "locate-krunner", "config.ini")


def read_config(path: str) -> dict[str, str]:
	config = ConfigParser()
	if not config.read(path):
		return {}
	if "Settings" in config:
		return dict(config["Settings"])
	return dict(config["DEFAULT"])


_GLOBAL_CFG = read_config(CONFIG_FILE)
CACHE_BIG = int(_GLOBAL_CFG.get("cache_big", "4096"))
CACHE_MED = int(_GLOBAL_CFG.get("cache_med", "2048"))


class LightResult(NamedTuple):
	path: str
	icon: str
	score: float
	subtext: str


@lru_cache(maxsize=CACHE_BIG)
def cached_path_metadata(path: str) -> tuple[bool, float | None, int, int]:
	try:
		stat_info = os.stat(path)
	except (OSError, FileNotFoundError):
		return False, None, 0, 0
	is_dir = (stat_info.st_mode & 0o170000) == 0o040000
	return is_dir, stat_info.st_mtime, stat_info.st_size, stat_info.st_mode


@lru_cache(maxsize=CACHE_BIG)
def cached_magic_mime(path: str) -> tuple[str, str]:
	try:
		mime_type = magic_from_file(path, mime=True)
		icon_name = mime_type.replace("/", "-")
		subtext = mime_type.split("/")[-1].upper()
		return sys.intern(icon_name), sys.intern(subtext)
	except (OSError, ValueError, TypeError):
		return sys.intern("unknown"), sys.intern("FILE")


@lru_cache(maxsize=CACHE_MED)
def get_icon_for_extension(filename: str) -> tuple[str, str]:
	try:
		guessed_type, _ = Gio.content_type_guess(filename, None)
		if guessed_type == "application/octet-stream" and "." in filename:
			_, ext = os.path.splitext(filename)
			subtext = ext[1:].upper() or "OCTET-STREAM"
			return sys.intern("unknown"), sys.intern(subtext)
		icon_theme = Gio.content_type_get_icon(guessed_type)
		icon_name = icon_theme.get_names()[0] if (icon_theme and icon_theme.get_names()) else "unknown"
		subtext = guessed_type.split("/")[-1].upper()
		return sys.intern(icon_name), sys.intern(subtext)
	except (TypeError, AttributeError, ValueError):
		return sys.intern("unknown"), sys.intern("FILE")


@lru_cache(maxsize=CACHE_MED)
def get_icon_and_subtext(path: str) -> tuple[str, str]:
	is_dir, _, _, _ = cached_path_metadata(path)
	if is_dir:
		return sys.intern("folder"), sys.intern("FOLDER")
	basename = os.path.basename(path)
	icon, subtext = get_icon_for_extension(basename)
	if subtext == "OCTET-STREAM" and MAGICMIME:
		return cached_magic_mime(path)
	return icon, subtext


class RelevanceScorer:
	def __init__(  # noqa: PLR0913, PLR0917
		self, rules: tuple, half_life_days: float, mod_time_weight: float, depth_penalty: float, exec_bonus: float, sigmoid_steepness: float
	) -> None:
		self.rules = rules
		self.mod_time_half_life = half_life_days * 86400.0
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
		age = max(0.0, now - mtime)
		return self.mod_time_weight * math.exp(-age / self.mod_time_half_life)

	def calculate(self, path: str, path_lower: str, words: tuple[str, ...], now: float) -> float:
		is_dir, mtime, size, mode = cached_path_metadata(path)
		if not is_dir and size == 0:
			return 0.0
		score = self._get_static_score(path, path_lower)
		name_lower = os.path.basename(path_lower)
		name_len = len(name_lower)
		matches = [
			math.pow(math.exp(-2.5 * name_lower.find(w) / name_len) * math.pow(len(w) / name_len, 0.7), 1.2) * 2.0 for w in words if w in name_lower
		]
		if matches:
			score += max(matches) + math.log1p(len(matches)) * 0.20
		if not is_dir:
			if mode & 0o111:
				score += self.exec_bonus
			score += self._modification_bonus(mtime, now)
		try:
			return 1.0 / (1.0 + math.exp(-score * self.sigmoid_steepness))
		except OverflowError:
			return 1.0 if score > 0 else 0.0


def parse_rules(config: dict[str, str], prefix: str) -> tuple:
	rules = []
	for key, value in config.items():
		if key.startswith(prefix) and ":" in value:
			pattern, score_str = value.rsplit(":", 1)
			with suppress(ValueError):
				score = float(score_str.strip())
				patterns = tuple(sys.intern(p.strip().lower()) for p in pattern.split("|"))
				rules.append((patterns, score))
	return tuple(rules)


def normalize_and_parse(query: str) -> tuple[str, tuple[str, ...]]:
	words = tuple(w.lower() for w in shlex_split(query))
	norm = " ".join(words)
	return norm, words


def build_dbus_response(results: list[LightResult]) -> list:
	return [(r.path, r.path, r.icon, 100, r.score, {"subtext": r.subtext}) for r in results]


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
	if len(words) <= 2:
		filtered = [r for r in results if all(w in r.path.lower() for w in words)]
		return build_dbus_response(filtered)
	regex = _compile_filter_regex(words)
	filtered = [r for r in results if regex.search(r.path)] if regex else [r for r in results if all(w in r.path.lower() for w in words)]

	return build_dbus_response(filtered)


def _spawn(cmd: list[str]) -> None:
	with suppress(OSError, subprocess.SubprocessError):
		subprocess.Popen(
			cmd,
			stdout=subprocess.DEVNULL,
			stderr=subprocess.DEVNULL,
			start_new_session=True,
		)


def _find_command(*candidates: str) -> str:
	for cmd in candidates:
		if found := shutil.which(cmd):
			return found
	return candidates[-1] if candidates else ""


def _copy_to_clipboard(text: str, clipboard_cmd: list[str] | None = None) -> None:
	if clipboard_cmd:
		try:
			subprocess.run(clipboard_cmd, input=text.encode('utf-8'), check=True, capture_output=True, timeout=2)
		except (subprocess.SubprocessError, OSError):
			pass
		else:
			return
	cmds = [
		["wl-copy"],
		["xclip", "-selection", "clipboard", "-in"],
		["xsel", "--clipboard", "--input"],
	]
	for cmd in cmds:
		if shutil.which(cmd[0]):
			try:
				subprocess.run(cmd, input=text.encode('utf-8'), check=True, capture_output=True, timeout=2)
			except (subprocess.SubprocessError, OSError):
				continue
			else:
				return


# ruff: disable[N802]
class Runner(dbus.service.Object):
	def __init__(self) -> None:
		bus_name = dbus.service.BusName("org.kde.locate", dbus.SessionBus())
		super().__init__(bus_name, "/runner")
		cfg = _GLOBAL_CFG
		requested_bin = cfg.get("binary")
		if requested_bin and shutil.which(requested_bin):
			self.binary = requested_bin
		else:
			self.binary = _find_command("plocate", "locate")
		opts_str = cfg.get("opts", "-i -l 25")
		if "-l" not in opts_str and "--limit" not in opts_str:
			opts_str += " -l 25"
		self.opts = tuple(shlex_split(opts_str))
		config_opener = cfg.get("opener")
		if config_opener:
			self.opener = shlex_split(config_opener)
		else:
			self.opener = [_find_command("mimeo", "handlr", "xdg-open")]
		config_clipboard = cfg.get("clipboard_cmd")
		if config_clipboard:
			self.clipboard_cmd = shlex_split(config_clipboard)
		else:
			self.clipboard_cmd = None
		self.min_len = max(1, int(cfg.get("min_len", "3")))
		self.debounce_ms = int(cfg.get("debounce_ms", "200"))
		self.process_timeout = float(cfg.get("process_timeout", "3.0"))
		self.max_cached_queries = int(cfg.get("history_size", "500"))
		rules = parse_rules(cfg, "scoring_rule_")
		self.scorer = RelevanceScorer(
			rules=rules,
			half_life_days=float(cfg.get("mod_time_half_life_days", "50")),
			mod_time_weight=float(cfg.get("mod_time_weight", "0.3")),
			depth_penalty=float(cfg.get("depth_penalty", "0.02")),
			exec_bonus=float(cfg.get("executable_bonus", "0.1")),
			sigmoid_steepness=float(cfg.get("sigmoid_steepness", "5.0")),
		)
		self.search_results = OrderedDict()
		self._current_query_norm: str | None = None
		self._query_lock = threading_Lock()
		self.executor = ThreadPoolExecutor(max_workers=1)
		self._debounce_timer: int | None = None
		self._last_emitted_count: int = 0

	@dbus.service.signal("org.kde.krunner1", signature="sa(sssida{sv})")
	def MatchesChanged(self, query: str, results: list) -> None:  # type: ignore[unused-parameter]
		pass

	def _update_cache(self, query: str, results: tuple[LightResult, ...]) -> None:
		if query in self.search_results:
			self.search_results.move_to_end(query)
		self.search_results[query] = results
		if len(self.search_results) > self.max_cached_queries:
			self.search_results.popitem(last=False)

	def _run_locate_job(self, norm_query: str, words: tuple[str, ...]) -> None:
		with self._query_lock:
			if self._current_query_norm != norm_query:
				return
		cmd = [self.binary, *self.opts, *words]
		try:
			res = subprocess.run(
				cmd,
				check=False,
				capture_output=True,
				text=True,
				timeout=self.process_timeout,
				errors="replace",
			)
			stdout = res.stdout
		except (subprocess.TimeoutExpired, OSError):
			return
		if not stdout:
			GLib.idle_add(self._on_search_finished, norm_query, ())
			return
		processed_results = []
		now = time_time()
		self._last_emitted_count = 0
		for i, path in enumerate(stdout.splitlines()):
			if i % 10 == 0:
				with self._query_lock:
					if self._current_query_norm != norm_query:
						return
			if not path:
				continue
			path_lower = path.lower()
			score = self.scorer.calculate(path, path_lower, words, now)
			if score > 0.01:
				icon, subtext = get_icon_and_subtext(path)
				processed_results.append(LightResult(path, icon, score, subtext))
			if i > 0 and i % 50 == 0 and len(processed_results) > self._last_emitted_count:
				with self._query_lock:
					if self._current_query_norm == norm_query:
						partial = sorted(
							processed_results,
							key=attrgetter("score"),
							reverse=True,
						)
						self._last_emitted_count = len(partial)
						GLib.idle_add(
							self.MatchesChanged,
							norm_query,
							build_dbus_response(partial),
						)
		processed_results.sort(key=attrgetter('score'), reverse=True)
		GLib.idle_add(self._on_search_finished, norm_query, tuple(processed_results))

	def _on_search_finished(self, query: str, results: tuple[LightResult, ...]) -> bool:
		with self._query_lock:
			is_current = self._current_query_norm == query
		if is_current:
			self._update_cache(query, results)
			if len(results) != self._last_emitted_count:
				GLib.idle_add(
					self.MatchesChanged,
					query,
					build_dbus_response(list(results)),
				)
		return False

	@dbus.service.method("org.kde.krunner1", in_signature="s", out_signature="a(sssida{sv})")
	def Match(self, query: str):  # noqa: ANN201
		stripped = query.strip()
		if len(stripped) < self.min_len:
			return []
		try:
			norm, words = normalize_and_parse(stripped)
		except ValueError:
			norm = stripped.lower()
			words = tuple(norm.split())
		if norm in self.search_results:
			self.search_results.move_to_end(norm)
			return build_dbus_response(self.search_results[norm])
		if self._debounce_timer:
			GLib.source_remove(self._debounce_timer)
		with self._query_lock:
			self._current_query_norm = norm
		self._debounce_timer = GLib.timeout_add(self.debounce_ms, self._debounce_callback, norm, words)
		if best_prev := self._find_best_prefix_match(norm):
			return filter_existing_results(best_prev, words)
		return []

	def _debounce_callback(self, norm_query: str, words: tuple[str, ...]) -> bool:
		self._debounce_timer = None
		self.executor.submit(self._run_locate_job, norm_query, words)
		return False

	def _find_best_prefix_match(self, current_query: str) -> tuple[LightResult, ...] | None:
		for key, results in reversed(self.search_results.items()):
			if current_query.startswith(key):
				return results
		return None

	@dbus.service.method("org.kde.krunner1", out_signature="a(sss)")
	def Actions(self):  # noqa: PLR6301, ANN201
		return [("open", "Open File", "document-open"), ("parent", "Open Parent Folder", "inode-directory"), ("copy", "Copy Path", "edit-copy")]

	@dbus.service.method("org.kde.krunner1", in_signature="ss")
	def Run(self, data: str, action_id: str) -> None:
		if not action_id or action_id == "open":
			_spawn([*self.opener, data])
		elif action_id == "parent":
			parent_dir = os.path.dirname(data)
			_spawn([*self.opener, parent_dir])
		elif action_id == "copy":
			_copy_to_clipboard(data, self.clipboard_cmd)


if __name__ == "__main__":
	signal.signal(signal.SIGINT, signal.SIG_DFL)
	Runner()
	loop = GLib.MainLoop()
	with suppress(KeyboardInterrupt):
		loop.run()
