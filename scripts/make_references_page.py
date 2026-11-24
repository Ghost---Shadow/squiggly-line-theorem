"""Write book/references.md from references.bib, the one bibliography of the repository.

    python scripts/make_references_page.py          # rewrite book/references.md
    python scripts/make_references_page.py --check  # fail if it is out of date

The paper reads references.bib through BibTeX. The book reads it through this
script: each entry becomes a small section whose heading is the BibTeX key, so
a chapter can link to it as `references.md#belkin2019reconciling`.

Two fields that BibTeX ignores record how far an entry has been checked:

    x-metadata-checked = {2026-11-11}   the paper exists, and its authors, title
                                        and year match arXiv or the publisher
    x-claim-checked    = {2026-11-24}   the claim this repository makes about the
                                        paper was read in the paper itself
    x-claim            = {...}          that claim, in one line

An entry without `x-claim-checked` is still "recalled" wherever it is cited.
"""
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIBLIOGRAPHY = ROOT / "references.bib"
PAGE = ROOT / "book" / "references.md"

ACCENTS = {"'": "́", "`": "̀", '"': "̈", "^": "̂", "~": "̃", "c": "̧", "v": "̌"}


def read_entries(text):
    """Return a list of (entry_type, key, fields) for every @entry in a .bib text."""
    entries = []
    position = 0
    while True:
        match = re.compile(r"@(\w+)\s*\{\s*([^,\s]+)\s*,").search(text, position)
        if match is None:
            return entries
        depth, index = 1, match.end()
        while depth > 0:
            depth += {"{": 1, "}": -1}.get(text[index], 0)
            index += 1
        body = text[match.end():index - 1]
        entries.append((match.group(1).lower(), match.group(2), read_fields(body)))
        position = index


def read_fields(body):
    """Read `name = {value}` and `name = number` pairs from the body of one entry."""
    fields = {}
    position = 0
    while True:
        match = re.compile(r"([\w-]+)\s*=\s*").search(body, position)
        if match is None:
            return fields
        index = match.end()
        if body[index] == "{":
            depth, start = 1, index + 1
            index += 1
            while depth > 0:
                depth += {"{": 1, "}": -1}.get(body[index], 0)
                index += 1
            value = body[start:index - 1]
        else:
            end = body.find(",", index)
            end = len(body) if end == -1 else end
            value, index = body[index:end].strip(), end
        fields[match.group(1).lower()] = " ".join(value.split())
        position = index


def to_plain_text(value):
    """Turn LaTeX accents such as {\\'e} into letters, and drop the other braces."""
    def put_accent(match):
        return unicodedata.normalize("NFC", match.group(2) + ACCENTS[match.group(1)])
    value = re.sub(r"\{?\\([\'`\"^~cv])\s*\{?(\w)\}?\}?", put_accent, value)
    value = value.replace("\\&", "&").replace("--", "–").replace("~", " ")
    return value.replace("{", "").replace("}", "")


def format_authors(author_field):
    names = []
    for author in to_plain_text(author_field).split(" and "):
        if "," in author:
            family, given = [part.strip() for part in author.split(",", 1)]
            names.append(f"{given} {family}")
        else:
            names.append(author.strip())
    if len(names) <= 2:
        return " and ".join(names)
    return ", ".join(names[:-1]) + " and " + names[-1]


def format_entry(entry_type, key, fields):
    lines = [f"#### {key}", ""]
    venue = fields.get("journal") or fields.get("booktitle") or fields.get("publisher") or fields.get("school") or ""
    parts = [f"{format_authors(fields.get('author', 'Unknown author'))} ({fields.get('year', 'no year')}).",
             f"*{to_plain_text(fields.get('title', 'Untitled'))}*."]
    if venue:
        parts.append(to_plain_text(venue) + ".")
    if "doi" in fields:
        parts.append(f"[doi:{fields['doi']}](https://doi.org/{fields['doi']}).")
    arxiv = fields.get("eprint") or (re.search(r"arXiv:(\S+)", fields.get("note", "")) or [None, None])[1]
    if arxiv:
        arxiv = arxiv.rstrip(".")
        parts.append(f"[arXiv:{arxiv}](https://arxiv.org/abs/{arxiv}).")
    lines.append(" ".join(parts))
    lines.append("")
    if "x-metadata-checked" in fields:
        status = f"Authors, title and year checked against the publisher or arXiv on {fields['x-metadata-checked']}."
    else:
        status = "Not yet checked against the publisher or arXiv."
    if "x-claim-checked" in fields:
        status += f" What this repository says about it was read in the paper on {fields['x-claim-checked']}."
    else:
        status += " What this repository says about it is **recalled**, not yet read in the paper."
    lines.append(status)
    if "x-claim" in fields:
        lines.append("")
        lines.append(f"Cited for: {to_plain_text(fields['x-claim'])}")
    lines.append("")
    return lines


def make_page():
    entries = read_entries(BIBLIOGRAPHY.read_text(encoding="utf-8"))
    keys = [key for _, key, _ in entries]
    assert len(keys) == len(set(keys)), "two entries share a key"
    entries.sort(key=lambda entry: (to_plain_text(entry[2].get("author", "")).lower(), entry[2].get("year", "")))
    lines = [
        "# References",
        "",
        "Every paper this repository cites, from the one file",
        "[`references.bib`](../references.bib) that the book and the paper both read.",
        "This page is written by [`scripts/make_references_page.py`](../scripts/make_references_page.py);",
        "edit the `.bib`, not this page.",
        "",
        "A reference is checked at two levels. The first is that the paper exists and",
        "its authors, title and year are right. The second is that what this",
        "repository says the paper shows was read in the paper itself. Until the",
        "second is done, the claim is marked **recalled** where it is made.",
        "",
        f"There are {len(entries)} entries. Chapters that cite a paper not yet listed here",
        "name it in the text, marked **recalled**.",
        "",
    ]
    for entry_type, key, fields in entries:
        lines.extend(format_entry(entry_type, key, fields))
    lines.append("Previous: [Glossary](glossary.md) · Next: [How to cite this book](how-to-cite.md)")
    return "\n".join(lines) + "\n"


def main():
    sys.stdout.reconfigure(encoding="utf-8")  # a Windows console may not be UTF-8
    page = make_page()
    if "--check" in sys.argv[1:]:
        current = PAGE.read_text(encoding="utf-8") if PAGE.exists() else ""
        if current != page:
            print("book/references.md is out of date: run python scripts/make_references_page.py")
            sys.exit(1)
        print("book/references.md is up to date")
        return
    PAGE.write_text(page, encoding="utf-8", newline="\n")
    print("wrote", PAGE.relative_to(ROOT).as_posix())


if __name__ == "__main__":
    main()
