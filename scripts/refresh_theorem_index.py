"""Claude Code hook: keep docs/theorem-index.md up to date.

The page is made by `python scripts/find_theorem.py index --write` from the
Lean sources and from the book chapters that mention each name. CI fails when
it is out of date. This hook rewrites it after any tool call that left one of
those files newer than the page, so nobody has to remember.

It is cheap when nothing changed: it only compares modification times. When a
source is newer it runs the tool (under a second), and it tells Claude if the
page's text changed, so that the page is committed with the change.

Setup, in .claude/settings.local.json (the file is not in git):

    {"hooks": {"PostToolUse": [{"matcher": "Write|Edit|Bash|PowerShell",
      "hooks": [{"type": "command",
                 "command": "python \\"$CLAUDE_PROJECT_DIR/scripts/refresh_theorem_index.py\\"",
                 "timeout": 30}]}]}}

Run it by hand to see what it would do, without the hook:

    python scripts/refresh_theorem_index.py --explain
"""

import json
import os
import subprocess
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
PAGE = REPOSITORY / "docs" / "theorem-index.md"
TOOL = REPOSITORY / "scripts" / "find_theorem.py"


def list_sources() -> list[Path]:
    """Every file the page is made from."""
    sources = [TOOL, REPOSITORY / "lean" / "SquigglyLine.lean", REPOSITORY / "lean" / "RENAMES-theorems.txt"]
    sources.extend((REPOSITORY / "lean" / "SquigglyLine").rglob("*.lean"))
    sources.extend((REPOSITORY / "book").glob("*.md"))
    return [source for source in sources if source.exists()]


def find_newer_sources() -> list[Path]:
    """The sources changed after the page was last written."""
    if not PAGE.exists():
        return list_sources()
    page_time = PAGE.stat().st_mtime
    return [source for source in list_sources() if source.stat().st_mtime > page_time]


def rewrite_page() -> bool:
    """Run the tool. True when the text of the page changed."""
    text_before = PAGE.read_bytes() if PAGE.exists() else b""
    subprocess.run(
        [sys.executable, str(TOOL), "index", "--write"],
        cwd=REPOSITORY, check=True, capture_output=True,
    )
    # The tool may leave an unchanged page alone. Mark it as checked, so that
    # the same sources do not count as newer on the next call.
    os.utime(PAGE)
    return PAGE.read_bytes() != text_before


def main() -> None:
    newer_sources = find_newer_sources()
    if "--explain" in sys.argv:
        names = [source.relative_to(REPOSITORY).as_posix() for source in newer_sources]
        print(f"sources newer than the page: {len(names)}")
        for name in names[:10]:
            print(f"  {name}")
        return
    if not newer_sources:
        return
    if rewrite_page():
        message = ("docs/theorem-index.md was rewritten by a hook, because a Lean file or a "
                   "book chapter changed. Commit it together with that change.")
        print(json.dumps({"hookSpecificOutput": {"hookEventName": "PostToolUse",
                                                 "additionalContext": message}}))


if __name__ == "__main__":
    main()
