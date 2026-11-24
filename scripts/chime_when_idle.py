"""Claude Code Stop hook: play a chime only when everything is idle, not at every stop.

Idle means: every background task the session started in the last 12 hours (subagents, background shell commands,
monitors) has reported back (a task notification with a final status, or a stop), and none of the listed busy programs
(by default Unity and Blender) is running. The hook reads the session's transcript (its path comes on stdin as JSON)
and never blocks the stop.

Setup, in .claude/settings.json:
    {"hooks": {"Stop": [{"hooks": [{"type": "command", "command": "python /path/to/chime_when_idle.py", "timeout": 40}]}]}}
Environment (optional):
    CHIME_FILE   the sound to play (default: chime.ogg beside this script); played with ffplay
    CHIME_BUSY   comma-separated process names that mean "still busy" (default: unity.exe,blender.exe;
                 the process check uses Windows' tasklist and is skipped elsewhere)
Check what it thinks is still running, without playing anything:
    python chime_when_idle.py --check <transcript.jsonl>
"""
import datetime as dt
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHIME = os.environ.get("CHIME_FILE", os.path.join(HERE, "chime.ogg"))
BUSY = [p.strip().lower() for p in os.environ.get("CHIME_BUSY", "unity.exe,blender.exe").split(",") if p.strip()]
WINDOW_HOURS = 12

STARTED = [
    re.compile(r"agentId: (\w+)"),
    re.compile(r"running in background with ID: (\w+)"),
    re.compile(r"moved to the background \(ID: (\w+)\)"),
    re.compile(r"Monitor started[^\n]*?ID: (\w+)"),
]
ENDED = [
    re.compile(r"<task-id>(\w+)</task-id>\s*(?:<tool-use-id>[^<]*</tool-use-id>\s*)?(?:<output-file>[^<]*</output-file>\s*)?<status>(?:completed|failed|killed|stopped|timed_out|cancelled)</status>"),
    re.compile(r"Successfully stopped task: (\w+)"),
    re.compile(r'"task_id":"(\w+)"'),
]


def texts(entry):
    """Every string inside a transcript entry, so a tool result's text is found wherever it nests."""
    if isinstance(entry, str):
        yield entry
    elif isinstance(entry, dict):
        for v in entry.values():
            yield from texts(v)
    elif isinstance(entry, list):
        for v in entry:
            yield from texts(v)


def running(transcript):
    since = dt.datetime.now(dt.timezone.utc) - dt.timedelta(hours=WINDOW_HOURS)
    started, ended = {}, set()
    with open(transcript, encoding="utf-8", errors="replace") as f:
        for line in f:
            try:
                entry = json.loads(line)
            except ValueError:
                continue
            stamp = entry.get("timestamp") if isinstance(entry, dict) else None
            try:
                when = dt.datetime.fromisoformat(stamp.replace("Z", "+00:00")) if stamp else None
            except ValueError:
                when = None
            for text in texts(entry):
                for pattern in STARTED:
                    for tid in pattern.findall(text):
                        if when is None or when >= since:
                            started.setdefault(tid, when)
                for pattern in ENDED:
                    ended.update(pattern.findall(text))
    return sorted(t for t in started if t not in ended)


def busy_processes():
    try:
        out = subprocess.run(["tasklist", "/FO", "CSV", "/NH"], capture_output=True, text=True, timeout=10).stdout.lower()
    except Exception:
        return []
    return [name for name in BUSY if f'"{name}"' in out]


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--check":
        left = running(sys.argv[2])
        print("still running:", left or "nothing", "| processes:", busy_processes() or "none")
        return
    try:
        data = json.load(sys.stdin)
    except Exception:
        data = {}
    transcript = data.get("transcript_path")
    if not transcript or not os.path.exists(transcript):
        return
    if running(transcript) or busy_processes():
        return
    try:
        subprocess.run(["ffplay", "-nodisp", "-autoexit", "-loglevel", "error", "-volume", "100", CHIME],
                       stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=20)
    except Exception:
        pass


if __name__ == "__main__":
    main()
