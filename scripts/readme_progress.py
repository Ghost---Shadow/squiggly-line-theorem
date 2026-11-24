"""Redraw the progress bar under the title of README.md, and the burn-down
chart in PROGRESS.md.

The bar is counted from the checklist in PROGRESS.md. Each item counts the
same:

    - [x] an item that is done               counts 1
    - [ ] an item that is not done           counts 0
    - [ ] an item that is part done (3 of 8) counts 3 / 8

The burn-down chart plots the items still to do against the date. Its points
come from git: the checklist as it stood in each commit that changed it, and
one more point for today when the file has changes that are not committed
yet. The ETA is a straight line through the first and the last point, run
down to zero. It is rough, and the page says how many days it rests on.

Run it after ticking an item:

    python scripts/readme_progress.py          # rewrite the bar and the chart
    python scripts/readme_progress.py --check  # fail if either is out of date
"""

import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
README = REPOSITORY / "README.md"
CHECKLIST = REPOSITORY / "PROGRESS.md"
CHART = REPOSITORY / "docs" / "burndown.svg"
BAR_CELLS = 20
MIN_DAYS_FOR_ETA = 0.25  # a shorter history says nothing about the pace

BAR_BLOCK = re.compile(
    r"(<!-- progress-bar:start -->\n).*?(<!-- progress-bar:end -->)", re.S
)
CHART_BLOCK = re.compile(
    r"(<!-- burndown:start -->\n).*?(<!-- burndown:end -->)", re.S
)
ITEM = re.compile(r"^- \[( |x)\] (.*)$")
PART_DONE = re.compile(r"\((\d+) of (\d+)\)")


@dataclass
class Point:
    moment: datetime
    items_left: float
    item_count: int


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
    return scores


def point_from(moment: datetime, checklist_text: str) -> Point | None:
    scores = read_scores(checklist_text)
    if not scores:
        return None
    return Point(moment, len(scores) - sum(scores), len(scores))


def run_git(*arguments: str) -> str:
    done = subprocess.run(
        ["git", *arguments], cwd=REPOSITORY, capture_output=True,
        encoding="utf-8", check=False,
    )
    return done.stdout if done.returncode == 0 else ""


def read_history(todays_text: str) -> list[Point]:
    """One point per commit that changed the checklist, oldest first."""
    log = run_git("log", "--reverse", "--format=%H %aI", "--",
                  CHECKLIST.name, README.name)
    points: list[Point] = []
    for line in log.splitlines():
        commit, moment_text = line.split()
        text = run_git("show", f"{commit}:{CHECKLIST.name}")
        if not text:  # before the checklist moved out of the README
            text = run_git("show", f"{commit}:{README.name}")
        point = point_from(datetime.fromisoformat(moment_text), text)
        if point is None:
            continue
        if points and (point.items_left, point.item_count) == (
            points[-1].items_left, points[-1].item_count
        ):
            continue  # nothing about the checklist changed in this commit
        points.append(point)
    committed = run_git("show", f"HEAD:{CHECKLIST.name}")
    if committed != todays_text:
        now_point = point_from(datetime.now().astimezone(), todays_text)
        if now_point is not None and (now_point.items_left, now_point.item_count) != (
            points[-1].items_left, points[-1].item_count
        ):
            points.append(now_point)
    return points


def read_now(points: list[Point]) -> datetime:
    """The date of the newest commit, so the same commit always draws the same
    chart. Days without ticked items after the last point slow the pace."""
    newest = run_git("log", "-1", "--format=%aI").strip()
    if not newest:
        return points[-1].moment
    return max(datetime.fromisoformat(newest), points[-1].moment)


def history_days(points: list[Point]) -> float:
    return (read_now(points) - points[0].moment).total_seconds() / 86400


def items_per_day(points: list[Point]) -> float | None:
    if history_days(points) < MIN_DAYS_FOR_ETA:
        return None
    pace = (points[0].items_left - points[-1].items_left) / history_days(points)
    return pace if pace > 0 else None


def eta_of(points: list[Point]) -> datetime | None:
    pace = items_per_day(points)
    if pace is None:
        return None
    return read_now(points) + timedelta(days=points[-1].items_left / pace)


def draw_bar_line(scores: list[float], points: list[Point]) -> str:
    share_done = sum(scores) / len(scores)
    filled_cells = round(share_done * BAR_CELLS)
    bar = "█" * filled_cells + "░" * (BAR_CELLS - filled_cells)
    eta = eta_of(points)
    eta_text = f"**ETA {eta:%Y-%m-%d}**" if eta else "ETA unknown"
    return (
        f"`{bar}` **{round(100 * share_done)}% done** · {eta_text} "
        f"([what this counts]({CHECKLIST.name}), "
        f"[burn-down]({CHECKLIST.name}#burn-down))\n"
    )


def draw_chart(points: list[Point]) -> str:
    """The burn-down chart as an SVG file: blue is measured, orange is the
    straight line to zero."""
    width, height = 640, 320
    left, right, top, bottom = 56, 24, 28, 44
    eta = eta_of(points)
    start = points[0].moment
    now = read_now(points)
    end = max(eta if eta else now, now)
    span_days = max((end - start).total_seconds() / 86400, 0.5)
    top_value = max(1, int(max(p.items_left for p in points)) + 1)

    def x_of(moment: datetime) -> float:
        days = (moment - start).total_seconds() / 86400
        return left + (width - left - right) * days / span_days

    def y_of(items: float) -> float:
        return top + (height - top - bottom) * (1 - items / top_value)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}"'
        f' font-family="sans-serif" font-size="12">',
        f'<rect width="{width}" height="{height}" fill="#ffffff"/>',
        f'<text x="{left}" y="18" font-size="14" font-weight="bold" '
        f'fill="#222">Items still to do</text>',
    ]
    for tick in range(0, top_value + 1, max(1, top_value // 6)):
        y = y_of(tick)
        parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y:.1f}" '
                     f'y2="{y:.1f}" stroke="#e4e4e4"/>')
        parts.append(f'<text x="{left - 8}" y="{y + 4:.1f}" text-anchor="end" '
                     f'fill="#555">{tick}</text>')
    day_ticks = max(1, round(span_days / 6))
    tick_day = start.date()
    while tick_day <= end.date():
        tick_moment = datetime.combine(tick_day, datetime.min.time(), start.tzinfo)
        if tick_moment >= start:
            x = x_of(tick_moment)
            parts.append(f'<text x="{x:.1f}" y="{height - 22}" '
                         f'text-anchor="middle" fill="#555">'
                         f'{tick_day:%d %b}</text>')
        tick_day += timedelta(days=day_ticks)
    if eta:
        parts.append(
            f'<line x1="{x_of(now):.1f}" '
            f'y1="{y_of(points[-1].items_left):.1f}" x2="{x_of(eta):.1f}" '
            f'y2="{y_of(0):.1f}" stroke="#dd8452" stroke-width="2" '
            f'stroke-dasharray="6 4"/>'
        )
        parts.append(
            f'<text x="{x_of(eta) - 6:.1f}" y="{y_of(0) - 20:.1f}" '
            f'text-anchor="end" fill="#dd8452" font-weight="bold">'
            f'ETA {eta:%d %b %Y}</text>'
        )
    path = " ".join(f"{x_of(p.moment):.1f},{y_of(p.items_left):.1f}"
                    for p in points + [Point(now, points[-1].items_left, 0)])
    parts.append(f'<polyline points="{path}" fill="none" stroke="#4c72b0" '
                 f'stroke-width="2.5"/>')
    for p in points:
        parts.append(f'<circle cx="{x_of(p.moment):.1f}" '
                     f'cy="{y_of(p.items_left):.1f}" r="4" fill="#4c72b0"/>')
    last = points[-1]
    parts.append(f'<text x="{x_of(last.moment) + 8:.1f}" '
                 f'y="{y_of(last.items_left) - 8:.1f}" fill="#4c72b0" '
                 f'font-weight="bold">{last.items_left:.1f} left</text>')
    parts.append("</svg>")
    return "\n".join(parts) + "\n"


def draw_chart_block(points: list[Point]) -> str:
    pace = items_per_day(points)
    eta = eta_of(points)
    as_of = read_now(points).date()
    if eta is None:
        verdict = (f"No ETA yet: the history covers {history_days(points):.1f} "
                   f"days, and no pace can be read from items ticked in it.")
    else:
        verdict = (
            f"**ETA {eta:%Y-%m-%d}.** {points[-1].items_left:.1f} items are "
            f"left, and the pace so far is {pace:.1f} items a day. That rests "
            f"on only {history_days(points):.1f} days of history, so treat it "
            f"as a guess, not a promise."
        )
    return (
        "![Burn-down chart: items still to do against the date, with the "
        "straight line to zero](docs/burndown.svg)\n\n"
        f"{verdict} As of {as_of:%Y-%m-%d}. The blue line is read from git "
        f"(every commit that changed this list); the dashed line is the "
        f"straight line to zero at that pace. When items are added to the "
        f"list the blue line goes up.\n"
    )


def replace_block(text: str, block: re.Pattern, new_body: str, name: str) -> str:
    if block.search(text) is None:
        sys.exit(f"missing the {name} block")
    return block.sub(lambda m: m.group(1) + new_body + m.group(2), text)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")  # the Windows console is not UTF-8
    readme_text = README.read_text(encoding="utf-8")
    checklist_text = CHECKLIST.read_text(encoding="utf-8")
    scores = read_scores(checklist_text)
    if not scores:
        sys.exit(f"{CHECKLIST.name} has no checklist items")
    points = read_history(checklist_text)
    bar_line = draw_bar_line(scores, points)
    new_readme = replace_block(readme_text, BAR_BLOCK, bar_line, "progress-bar")
    new_checklist = replace_block(checklist_text, CHART_BLOCK,
                                  draw_chart_block(points), "burndown")
    chart_svg = draw_chart(points)
    old_chart = CHART.read_text(encoding="utf-8") if CHART.exists() else ""
    if "--check" in sys.argv:
        if (new_readme, new_checklist, chart_svg) != (
            readme_text, checklist_text, old_chart
        ):
            sys.exit("the progress bar or the chart is out of date: "
                     "run scripts/readme_progress.py")
        print("up to date:", bar_line.strip())
        return
    # Write a file only when its text changes. A file watcher (the FileChanged
    # hook on PROGRESS.md) runs this script on every write, so a write that
    # changes nothing would run it again, for ever.
    for path, old_text, new_text in (
        (README, readme_text, new_readme),
        (CHECKLIST, checklist_text, new_checklist),
        (CHART, old_chart, chart_svg),
    ):
        if new_text != old_text:
            path.write_text(new_text, encoding="utf-8", newline="\n")
    print(bar_line.strip())


if __name__ == "__main__":
    main()
