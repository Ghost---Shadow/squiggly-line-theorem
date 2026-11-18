"""Redraw the progress bar under the title of README.md.

The bar is counted from the checklist in PROGRESS.md. Each item counts the
same:

    - [x] an item that is done               counts 1
    - [ ] an item that is not done           counts 0
    - [ ] an item that is part done (3 of 8) counts 3 / 8

Run it after ticking an item:

    python scripts/readme_progress.py          # rewrite the bar
    python scripts/readme_progress.py --check  # fail if the bar is out of date
"""

import re
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
README = REPOSITORY / "README.md"
CHECKLIST = REPOSITORY / "PROGRESS.md"
BAR_CELLS = 20

BAR_BLOCK = re.compile(
    r"(<!-- progress-bar:start -->\n).*?(<!-- progress-bar:end -->)", re.S
)
ITEM = re.compile(r"^- \[( |x)\] (.*)$")
PART_DONE = re.compile(r"\((\d+) of (\d+)\)")


def score_of_item(is_ticked: bool, text: str) -> float:
    if is_ticked:
        return 1.0
    part_done = PART_DONE.search(text)
    if part_done is None:
        return 0.0
    done_count, whole_count = int(part_done.group(1)), int(part_done.group(2))
    return done_count / whole_count


def read_scores(checklist_text: str) -> list[float]:
    scores = []
    for line in checklist_text.splitlines():
        item = ITEM.match(line)
        if item is not None:
            scores.append(score_of_item(item.group(1) == "x", item.group(2)))
    if not scores:
        sys.exit(f"{CHECKLIST.name} has no checklist items")
    return scores


def draw_bar_line(scores: list[float]) -> str:
    share_done = sum(scores) / len(scores)
    filled_cells = round(share_done * BAR_CELLS)
    bar = "█" * filled_cells + "░" * (BAR_CELLS - filled_cells)
    return (
        f"`{bar}` **{round(100 * share_done)}% done** "
        f"([what this counts]({CHECKLIST.name}))\n"
    )


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")  # the Windows console is not UTF-8
    readme_text = README.read_text(encoding="utf-8")
    scores = read_scores(CHECKLIST.read_text(encoding="utf-8"))
    bar_line = draw_bar_line(scores)
    if BAR_BLOCK.search(readme_text) is None:
        sys.exit("README.md has no progress-bar block")
    new_text = BAR_BLOCK.sub(lambda block: block.group(1) + bar_line + block.group(2),
                             readme_text)
    if "--check" in sys.argv:
        if new_text != readme_text:
            sys.exit("the progress bar is out of date: run scripts/readme_progress.py")
        print("up to date:", bar_line.strip())
        return
    README.write_text(new_text, encoding="utf-8", newline="\n")
    print(bar_line.strip())


if __name__ == "__main__":
    main()
