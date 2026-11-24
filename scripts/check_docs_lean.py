"""Check what docs/ and the README say about the Lean sources.

    python scripts/check_docs_lean.py                 # every file
    python scripts/check_docs_lean.py docs/networks   # only files under a path

The checks are the ones book/tools/check_book.py applies to the chapters of
the book, here applied to docs/**/*.md and README.md:

1. every line inside a ```lean block is a whole line of some Lean file;
2. every name in backticks that looks like a Lean name (it has an
   underscore) exists in the Lean files. A miss is a problem for a name with
   capitals and a warning for an all-lowercase name, which may be a made-up
   local name in a formula;
3. every relative link resolves, and every #anchor exists.

So a theorem that was renamed or removed, a Lean file that was moved, and a
quoted statement that was edited in the source all show up here.
"""
import importlib.util
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

spec = importlib.util.spec_from_file_location(
    "check_book", ROOT / "book" / "tools" / "check_book.py"
)
check_book = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_book)


def main():
    sys.stdout.reconfigure(encoding="utf-8")  # a Windows console may not be UTF-8
    wanted = [(ROOT / argument).resolve() for argument in sys.argv[1:]]
    files = sorted((ROOT / "docs").rglob("*.md")) + [ROOT / "README.md"]
    if wanted:
        files = [
            path for path in files
            if any(folder == path or folder in path.parents for folder in wanted)
        ]
    total = 0
    for path in files:
        problems, warnings, _pending = check_book.check(path)
        total += len(problems)
        name = path.relative_to(ROOT).as_posix()
        for kind, detail in problems:
            print(f"PROBLEM  {name}: {kind}: {detail}")
        for kind, detail in warnings:
            print(f"warning  {name}: {kind}: {detail}")
        print(f"checked  {name}")
    print("problems:", total)
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
