"""Rename theorems everywhere they are named, from lean/RENAMES-theorems.txt.

    python scripts/rename_theorems.py            # apply every pair
    python scripts/rename_theorems.py --check    # fail if an old name is still in use
    python scripts/rename_theorems.py --dry-run  # say what would change

Each line of the mapping is `old_name new_name`. A name is replaced only where
it stands as a whole name: not inside a longer name. The files touched are the
Lean sources, the Markdown of the book (not its proposals), docs/, the README,
the paper (where an underscore is written `\\_`), and the notebooks and scripts
of experiments/.

After a run, build Lean (`lake build` in lean/) and run the two text checks
(`book/tools/check_book.py`, `scripts/check_docs_lean.py`). A rename never
changes the mathematics, so the build must pass exactly as before.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAPPING = ROOT / "lean" / "RENAMES-theorems.txt"
NAME_CHARACTER = r"[A-Za-z0-9_']"


def read_mapping():
    pairs = []
    for line in MAPPING.read_text(encoding="utf-8").split("\n"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        old_name, new_name = line.split()
        pairs.append((old_name, new_name))
    old_names = [old for old, _ in pairs]
    assert len(old_names) == len(set(old_names)), "an old name is listed twice"
    return pairs


def list_files():
    files = []
    for path in (ROOT / "lean").rglob("*.lean"):
        if ".lake" not in path.parts:
            files.append(path)
    files += [path for path in (ROOT / "lean").glob("*.md")]
    files += [path for path in (ROOT / "book").glob("*.md")]
    files += list((ROOT / "docs").rglob("*.md"))
    files += [ROOT / "README.md", ROOT / "CONTRIBUTING.md"]
    files += list((ROOT / "paper").rglob("*.tex"))
    files += list((ROOT / "experiments").rglob("*.ipynb"))
    files += list((ROOT / "experiments").rglob("*.py"))
    return sorted(set(files))


def make_pattern(old_name):
    """Match the name only where no name character touches it on either side."""
    return re.compile(rf"(?<!{NAME_CHARACTER}){re.escape(old_name)}(?!{NAME_CHARACTER})")


def rename_in_text(text, pairs, is_latex):
    count = 0
    for old_name, new_name in pairs:
        if is_latex:
            old_name, new_name = old_name.replace("_", "\\_"), new_name.replace("_", "\\_")
            pattern = re.compile(
                rf"(?<![A-Za-z0-9']){re.escape(old_name)}(?!(?:\\_|[A-Za-z0-9']))"
            )
        else:
            pattern = make_pattern(old_name)
        text, replaced = pattern.subn(lambda _match: new_name, text)
        count += replaced
    return text, count


def main():
    sys.stdout.reconfigure(encoding="utf-8")  # a Windows console may not be UTF-8
    check_only = "--check" in sys.argv[1:]
    dry_run = "--dry-run" in sys.argv[1:]
    pairs = read_mapping()
    # Longer old names first, so a name that is the start of another is not cut.
    pairs.sort(key=lambda pair: -len(pair[0]))
    total = 0
    for path in list_files():
        text = path.read_text(encoding="utf-8")
        new_text, count = rename_in_text(text, pairs, is_latex=path.suffix == ".tex")
        if count == 0:
            continue
        total += count
        print(f"{path.relative_to(ROOT).as_posix()}: {count}")
        if not check_only and not dry_run:
            path.write_text(new_text, encoding="utf-8", newline="\n")
    if check_only:
        print("old names still in use:", total)
        sys.exit(1 if total else 0)
    print(("would rename" if dry_run else "renamed"), total, "uses of", len(pairs), "names")


if __name__ == "__main__":
    main()
