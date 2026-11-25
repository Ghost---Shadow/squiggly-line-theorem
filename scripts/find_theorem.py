"""Search the theorems, definitions and proofs of the Lean library.

An agent (or a person) who cannot hold the whole library in context can ask
this tool where a theorem is, what it says, what uses it and where the book
quotes it, without reading whole Lean files.

    python scripts/find_theorem.py search share token       # ranked keyword search
    python scripts/find_theorem.py show every_token_gets_a_share --used-by
    python scripts/find_theorem.py define COVERS_WITHIN
    python scripts/find_theorem.py file AttentionRate
    python scripts/find_theorem.py chapter 36
    python scripts/find_theorem.py stats
    python scripts/find_theorem.py index --write            # rewrite docs/theorem-index.md
    python scripts/find_theorem.py index --check            # fail if that page is stale
    python scripts/find_theorem.py selftest                 # checks the tool against the sources

It reads the sources directly on every run (standard library only, no Lean
build, no network, no cache) and takes well under two seconds.

What it reads:

* lean/SquigglyLine/**/*.lean and lean/SquigglyLine.lean (the folders named
  Tests are skipped unless --include-tests is given);
* book/*.md, docs/**/*.md, README.md, paper/**/*.tex, experiments/**/*.ipynb
  and experiments/**/*.py, to find where each name is mentioned;
* lean/RENAMES-theorems.txt, so that an old name finds the new one.

Run `python scripts/find_theorem.py --help` for the examples and for what the
tool does not do.
"""
from __future__ import annotations

import argparse
import bisect
import contextlib
import dataclasses
import difflib
import io
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FOLDER = ROOT / "lean" / "SquigglyLine"
LEAN_ROOT_FILE = ROOT / "lean" / "SquigglyLine.lean"
RENAMES_FILE = ROOT / "lean" / "RENAMES-theorems.txt"
INDEX_PAGE = ROOT / "docs" / "theorem-index.md"

ROOT_NAMESPACE = "SquigglyLine"
DEFINITION_KINDS = ("def", "abbrev", "structure", "class", "inductive", "instance")
KIND_GROUPS = {"theorem": ("theorem", "lemma")}
SKIPPED_TEXT_LINE_LENGTH = 5000  # a line this long is a picture in a notebook, not text

EPILOG = """\
examples:
  find_theorem.py search share token              names, docs and statements, best first
  find_theorem.py search --statement LipschitzWith --folder Networks
  find_theorem.py search average --kind def --limit 5
  find_theorem.py search softmax --in-proofs      also look inside the proofs
  find_theorem.py search share token --json       the same data as JSON
  find_theorem.py show every_token_gets_a_share --proof --used-by
  find_theorem.py show nearestDist_nonneg         an old name finds the new one
  find_theorem.py define COVERS_WITHIN            a definition and the theorems about it
  find_theorem.py file Attention                  one file: header and a line per declaration
  find_theorem.py chapter 36                      the Lean names that book chapter 36 mentions
  find_theorem.py stats                           counts, undocumented and unused theorems
  find_theorem.py index --check                   is docs/theorem-index.md up to date?

Output is YAML (keys with empty values are left out, Lean text is in block
scalars). Every sub-command also takes --json, which prints every key. A search
hit in YAML is name, at (path:line) and doc, with kind unless it is a
theorem; `more: N` counts the hits not shown. Exit code 0 with hits, 1 with
none, 2 on a usage error. When no
declaration matches all the words, the first key is `note`, and the partial
matches follow with exit 0.

what this does not do:
  * It does not know Mathlib. A name that is not declared under
    lean/SquigglyLine is not in the index.
  * Cross references are by name. A name used only through `open`, through an
    alias, through a macro or through a structure projection such as
    `random_model.marginal` is matched only when the declared name is dotted
    and the last part is unique or the namespace is the current one.
  * A name inside a comment or a string is not a use. A theorem used by
    `simp` or `exact?` without being named is not a use.
  * Book, docs and paper mentions are whole-name matches, so a name that
    is cut over a line break is missed. A name without an underscore (a Model,
    a Cost) counts in book and docs only inside backticks.
  * A statement ends at the first `:=` that no `let` has used and that is not
    inside brackets; a declaration with a different shape may be cut wrongly.
"""


# --------------------------------------------------------------------------
# Data
# --------------------------------------------------------------------------


@dataclasses.dataclass
class Mention:
    """One place outside Lean where a name appears."""

    path: str
    line: int
    chapter: int | None  # the book chapter number, when the file is a chapter


@dataclasses.dataclass
class Declaration:
    """One top-level declaration of a Lean file."""

    identifier: int
    name: str  # as written
    qualified: str  # with every namespace
    display: str  # qualified, without the leading SquigglyLine.
    keyword: str  # theorem, lemma, def, abbrev, structure, class, instance, inductive
    kind: str  # the keyword; kept apart in case a kind is ever merged
    modifiers: list[str]
    attributes: str
    path: str
    folder: str
    line: int  # first line, attribute line included
    end_line: int
    doc: str
    doc_line: int
    section: str
    statement: str
    proof: str
    proof_lines: int
    namespaces: tuple[str, ...]
    masked_statement: str
    masked_proof: str
    file: "SourceFile | None" = None
    uses: set[int] = dataclasses.field(default_factory=set)
    mentions: set[int] = dataclasses.field(default_factory=set)
    used_by: set[int] = dataclasses.field(default_factory=set)
    mentioned_by: set[int] = dataclasses.field(default_factory=set)
    text_mentions: list[Mention] = dataclasses.field(default_factory=list)
    renamed_from: list[str] = dataclasses.field(default_factory=list)

    @property
    def is_theorem(self) -> bool:
        return self.kind in KIND_GROUPS["theorem"]

    @property
    def is_definition(self) -> bool:
        return self.kind in DEFINITION_KINDS


@dataclasses.dataclass
class SourceFile:
    """One Lean file: its header and its declarations."""

    path: str
    folder: str
    header: str
    title: str
    declarations: list[Declaration] = dataclasses.field(default_factory=list)
    imports: list[str] = dataclasses.field(default_factory=list)  # module names
    closure: set[str] = dataclasses.field(default_factory=set)  # paths this file may use


@dataclasses.dataclass
class Index:
    """Everything the sub-commands need."""

    files: dict[str, SourceFile]
    declarations: list[Declaration]
    by_display: dict[str, list[Declaration]]
    by_qualified: dict[str, list[Declaration]]
    by_last: dict[str, list[Declaration]]
    renames: dict[str, str]  # old name -> new name
    text_files_read: int


# --------------------------------------------------------------------------
# Reading Lean: comments, strings, and the top-level layout
# --------------------------------------------------------------------------

CODE_TOKEN = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\\n])*"')
COMMENT_TOKEN = re.compile(r"/-|-/")
NOT_NEWLINE = re.compile(r"[^\n]")


def blank_out(text: str) -> str:
    """Replace every character but newlines by a space, keeping the layout."""
    return NOT_NEWLINE.sub(" ", text)


def mask_comments_and_strings(text: str) -> tuple[str, list[tuple[int, int]]]:
    """Return the text with comments and strings blanked, and the block comments.

    The masked text has the same length and the same line breaks as the
    original, so an offset or a line number in one is valid in the other. The
    second result lists the outermost block comments as (start, end) offsets.
    """
    pieces: list[str] = []
    blocks: list[tuple[int, int]] = []
    position = 0
    while position < len(text):
        match = CODE_TOKEN.search(text, position)
        if match is None:
            pieces.append(text[position:])
            break
        pieces.append(text[position:match.start()])
        if match.group() == "/-":
            depth = 1
            cursor = match.end()
            while depth > 0:
                inner = COMMENT_TOKEN.search(text, cursor)
                if inner is None:
                    cursor = len(text)
                    break
                depth += 1 if inner.group() == "/-" else -1
                cursor = inner.end()
            end = cursor
            blocks.append((match.start(), end))
        else:
            end = match.end()
        pieces.append(blank_out(text[match.start():end]))
        position = end
    return "".join(pieces), blocks


DECLARATION_START = re.compile(
    r"""^(?P<attributes>(?:@\[[^\]]*\]\s*)*)
        (?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*)
        (?P<keyword>theorem|lemma|def|abbrev|structure|class|instance|inductive)\b""",
    re.VERBOSE,
)
ATTRIBUTE_ONLY = re.compile(r"^@\[[^\]]*\]\s*$")
NAME_AFTER_KEYWORD = re.compile(r"^\s+([^\s(\[{:⦃⟨]+)")
IMPORT_COMMAND = re.compile(r"^import\s+(\S+)")
NAMESPACE_COMMAND = re.compile(r"^namespace\s+(\S+)")
SECTION_COMMAND = re.compile(r"^section\b\s*(\S*)")
END_COMMAND = re.compile(r"^end\b")
HEADING = re.compile(r"^\s*#{1,6}\s+(.*?)\s*$")
SPLIT_TOKEN = re.compile(r"[(\[{⟨⦃]|[)\]}⟩⦄]|:=|(?<![\w'.])let(?![\w'])|(?<![\w'.])where(?![\w'])")
OPENERS = "([{⟨⦃"
LINE_STARTING_BAR = re.compile(r"^\s+\|", re.MULTILINE)


def split_declaration(masked: str, keyword: str) -> tuple[int, int]:
    """Find where the statement ends and the proof (or body) begins.

    The statement ends at the first `:=` outside brackets that no `let` has
    used up: in this project a statement is a column of `let name := value`
    lines followed by the claim. A structure or an instance may use `where`
    instead. Returns (end of statement, start of proof), both offsets into
    `masked`. With no such mark the whole text is the statement.
    """
    depth = 0
    pending_lets = 0
    for match in SPLIT_TOKEN.finditer(masked):
        token = match.group()
        if token in OPENERS and len(token) == 1:
            depth += 1
        elif token in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth > 0:
            continue
        elif token == "let":
            pending_lets += 1
        elif token == ":=":
            if pending_lets > 0:
                pending_lets -= 1
            else:
                return match.start(), match.end()
        elif token == "where" and keyword not in ("theorem", "lemma"):
            return match.start(), match.end()
    first_line_end = masked.find("\n")
    bar = LINE_STARTING_BAR.search(masked, first_line_end if first_line_end >= 0 else 0)
    if bar is not None:
        return bar.start(), bar.start()
    return len(masked), len(masked)


def parse_source_file(path: Path) -> SourceFile:
    """Read one Lean file into a SourceFile with its declarations."""
    relative = path.relative_to(ROOT).as_posix()
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
    masked, block_spans = mask_comments_and_strings(text)
    lines = text.split("\n")
    masked_lines = masked.split("\n")
    line_starts = [0]
    for line in lines:
        line_starts.append(line_starts[-1] + len(line) + 1)

    def line_of(offset: int) -> int:
        return bisect.bisect_right(line_starts, offset) - 1  # zero-based

    doc_by_end_line: dict[int, tuple[int, str]] = {}
    headings: list[tuple[int, str]] = []
    header = ""
    first_command_line = next(
        (index for index, line in enumerate(masked_lines) if line.strip() and not line[0].isspace()),
        len(lines),
    )
    for start, end in block_spans:
        opening = text[start:start + 3]
        body = text[start:end]
        first_line, last_line = line_of(start), line_of(end - 1)
        if opening == "/--":
            doc = body[3:-2].strip() if body.endswith("-/") else body[3:].strip()
            doc_by_end_line[last_line] = (first_line, doc)
        elif opening == "/-!":
            inner = body[3:-2] if body.endswith("-/") else body[3:]
            for offset, line in enumerate(inner.split("\n")):
                heading = HEADING.match(line)
                if heading:
                    headings.append((first_line + offset, heading.group(1)))
        elif not header and first_line < first_command_line:
            header = body[2:-2].strip("\n") if body.endswith("-/") else body[2:]
    title = next((line.strip() for line in header.split("\n") if line.strip()), "")
    heading_lines = [line for line, _ in headings]

    folder = path.parent.relative_to(LEAN_FOLDER).as_posix() if LEAN_FOLDER in path.parents else ""
    source = SourceFile(relative, "" if folder == "." else folder, header, title)
    for masked_line in masked_lines:
        import_match = IMPORT_COMMAND.match(masked_line)
        if import_match:
            source.imports.append(import_match.group(1))

    commands = [
        index for index, line in enumerate(masked_lines)
        if line.strip() and not line[0].isspace()
    ]
    frames: list[tuple[str, str]] = []
    pending_attribute_line: int | None = None
    for position, index in enumerate(commands):
        line = masked_lines[index]
        next_index = commands[position + 1] if position + 1 < len(commands) else len(lines)
        namespace_match = NAMESPACE_COMMAND.match(line)
        if namespace_match:
            frames.append(("namespace", namespace_match.group(1)))
            pending_attribute_line = None
            continue
        section_match = SECTION_COMMAND.match(line)
        if section_match:
            frames.append(("section", section_match.group(1)))
            pending_attribute_line = None
            continue
        if END_COMMAND.match(line):
            if frames:
                frames.pop()
            pending_attribute_line = None
            continue
        if ATTRIBUTE_ONLY.match(line):
            pending_attribute_line = index
            continue
        start_match = DECLARATION_START.match(line)
        if not start_match:
            pending_attribute_line = None
            continue

        keyword = start_match.group("keyword")
        modifiers = start_match.group("modifiers").split()
        attributes = start_match.group("attributes").strip()
        first_index = index
        if pending_attribute_line is not None and pending_attribute_line < index:
            first_index = pending_attribute_line
            attributes = (masked_lines[pending_attribute_line].strip() + " " + attributes).strip()
        pending_attribute_line = None

        name_match = NAME_AFTER_KEYWORD.match(line[start_match.end():])
        name = name_match.group(1) if name_match else f"{keyword}@{index + 1}"
        namespaces = tuple(
            part for kind, frame in frames if kind == "namespace" for part in frame.split(".")
        )
        if name.startswith("_root_."):
            name = name[len("_root_."):]
            qualified = name
        else:
            qualified = ".".join(namespaces + (name,))
        display = qualified[len(ROOT_NAMESPACE) + 1:] if qualified.startswith(ROOT_NAMESPACE + ".") else qualified

        last_index = index
        for candidate in range(next_index - 1, index - 1, -1):
            if masked_lines[candidate].strip():
                last_index = candidate
                break
        column = start_match.end("attributes")
        original_text = "\n".join(lines[index:last_index + 1])[column:]
        masked_text = "\n".join(masked_lines[index:last_index + 1])[column:]
        statement_end, proof_start = split_declaration(masked_text, keyword)
        statement = original_text[:statement_end].rstrip()
        proof = original_text[proof_start:].lstrip(" \t")
        if proof.startswith("\n"):
            proof = proof[1:]
        proof = proof.rstrip()
        proof_first_line = index + masked_text.count("\n", 0, proof_start)
        proof_lines = (last_index - proof_first_line + 1) if proof else 0

        doc, doc_line = "", 0
        before = first_index - 1
        while before >= 0 and not lines[before].strip():
            before -= 1
        if before in doc_by_end_line:
            doc_line, doc = doc_by_end_line[before][0] + 1, doc_by_end_line[before][1]
        slot = bisect.bisect_left(heading_lines, first_index) - 1
        section = headings[slot][1] if slot >= 0 else ""

        declaration = Declaration(
            identifier=-1, name=name, qualified=qualified, display=display,
            keyword=keyword, kind=keyword, modifiers=modifiers, attributes=attributes,
            path=relative, folder=source.folder, line=first_index + 1, end_line=last_index + 1,
            doc=doc, doc_line=doc_line, section=section, statement=statement, proof=proof,
            proof_lines=proof_lines, namespaces=namespaces,
            masked_statement=masked_text[:statement_end], masked_proof=masked_text[proof_start:],
            file=source,
        )
        source.declarations.append(declaration)
    return source


def lean_paths(include_tests: bool) -> list[Path]:
    """The Lean files to index, in a fixed order."""
    paths = [LEAN_ROOT_FILE] + sorted(LEAN_FOLDER.rglob("*.lean"), key=lambda path: path.as_posix())
    wanted = []
    for path in paths:
        if ".lake" in path.parts or "scratch" in path.parts:
            continue
        if "Tests" in path.parts and not include_tests:
            continue
        wanted.append(path)
    return wanted


# --------------------------------------------------------------------------
# Cross references
# --------------------------------------------------------------------------

LEAN_TOKEN = re.compile(r"\.?[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")


def resolve_lean_token(
    index: Index, token: str, namespaces: tuple[str, ...], allowed: set[str]
) -> list[Declaration]:
    """The declarations a token in Lean code may stand for.

    A token is tried as a name in the current namespace and the ones around it,
    then as a name with its head cut off at each dot (`COVERS_WITHIN.foo` may
    be `COVERS_WITHIN` followed by a projection), and a dotted call such as
    `(foo args).compress` or `value.compress` by the last part when a dotted
    declaration ends in it. Only declarations of the same file, or of a file
    it imports (directly or not), can be meant: `allowed` holds those paths.
    """
    is_dot_call = token.startswith(".")
    core = token.lstrip(".")
    found: list[Declaration] = []
    if not is_dot_call:
        parts = core.split(".")
        for length in range(len(parts), 0, -1):
            head = ".".join(parts[:length])
            for cut in range(len(namespaces), -1, -1):
                candidate = ".".join(namespaces[:cut] + (head,))
                here = [d for d in index.by_qualified.get(candidate, []) if d.path in allowed]
                if here:
                    found.extend(here)
                    break
            if found:
                break
    if is_dot_call or "." in core:
        last = core.rsplit(".", 1)[-1]
        for declaration in index.by_last.get(last, []):
            if declaration.path in allowed and declaration not in found:
                found.append(declaration)
    return found


def find_references(
    index: Index, masked_text: str, namespaces: tuple[str, ...], own: int, allowed: set[str]
) -> set[int]:
    """The identifiers of the declarations a piece of masked Lean text names."""
    cache: dict[str, list[Declaration]] = {}
    references: set[int] = set()
    for match in LEAN_TOKEN.finditer(masked_text):
        token = match.group()
        if token not in cache:
            cache[token] = resolve_lean_token(index, token, namespaces, allowed)
        for declaration in cache[token]:
            if declaration.identifier != own:
                references.add(declaration.identifier)
    return references


# --------------------------------------------------------------------------
# Reading text outside Lean
# --------------------------------------------------------------------------

TEXT_TOKEN = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
CODE_SPAN = re.compile(r"`[^`\n]+`")


def text_file_paths() -> list[Path]:
    """The files in which a mention of a Lean name is looked for."""
    paths: list[Path] = []
    paths += sorted((ROOT / "book").glob("*.md"))
    paths += sorted(path for path in (ROOT / "docs").rglob("*.md") if path != INDEX_PAGE)
    if (ROOT / "README.md").exists():
        paths.append(ROOT / "README.md")
    paths += sorted((ROOT / "paper").rglob("*.tex"))
    for pattern in ("*.ipynb", "*.py"):
        paths += sorted(
            path for path in (ROOT / "experiments").rglob(pattern)
            if ".ipynb_checkpoints" not in path.parts
        )
    return paths


def chapter_number(relative: str) -> int | None:
    match = re.match(r"book/(\d+)-[^/]*\.md$", relative)
    return int(match.group(1)) if match else None


def tail_aliases(declarations: list[Declaration]) -> dict[str, Declaration]:
    """A dotted name whose last part is a long name with an underscore and is
    unique, so that a text may write the last part alone."""
    counts: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        counts[declaration.display.rsplit(".", 1)[-1]].append(declaration)
    aliases = {}
    for last, group in counts.items():
        if len(group) == 1 and "_" in last and "." in group[0].display:
            aliases[last] = group[0]
    return aliases


def collect_text_mentions(index: Index) -> int:
    """Fill `text_mentions` of every declaration. Returns how many files were read."""
    aliases = tail_aliases(index.declarations)
    paths = text_file_paths()
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        is_markdown = path.suffix == ".md"
        if path.suffix == ".tex":
            text = text.replace("\\_", "_")
        elif is_markdown:
            text = text.replace("\\_", "_")
        chapter = chapter_number(relative)
        seen: set[tuple[int, int]] = set()
        offset = 0
        for line_number, line in enumerate(text.split("\n"), start=1):
            line_offset = offset
            offset += len(line) + 1
            if len(line) > SKIPPED_TEXT_LINE_LENGTH or not line.strip():
                continue
            spans = None
            for match in TEXT_TOKEN.finditer(line):
                token = match.group()
                if token.startswith(ROOT_NAMESPACE + "."):
                    token = token[len(ROOT_NAMESPACE) + 1:]
                matched = index.by_display.get(token) or index.by_qualified.get(token)
                if not matched and token in aliases:
                    matched = [aliases[token]]
                if not matched:
                    continue
                if "_" not in token and "." not in token:
                    if not is_markdown:
                        continue
                    if spans is None:
                        spans = [(span.start(), span.end()) for span in CODE_SPAN.finditer(line)]
                    if not any(start < match.start() and match.end() < end for start, end in spans):
                        continue
                for declaration in matched:
                    key = (declaration.identifier, line_number)
                    if key in seen:
                        continue
                    seen.add(key)
                    declaration.text_mentions.append(Mention(relative, line_number, chapter))
    return len(paths)


def read_renames() -> dict[str, str]:
    """The pairs `old_name new_name` of lean/RENAMES-theorems.txt."""
    renames: dict[str, str] = {}
    if not RENAMES_FILE.exists():
        return renames
    for line in RENAMES_FILE.read_text(encoding="utf-8").split("\n"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) == 2:
            renames[parts[0]] = parts[1]
    return renames


def follow_rename(index: Index, name: str) -> list[Declaration]:
    """The declarations an old name stands for now; empty when it is not an old name.

    Follows a chain of renames. A new name written without its namespace (a
    theorem inside `namespace HAS_TIGHT_FEATURES`) is found by its last part.
    """
    seen = set()
    current = name
    while current in index.renames and current not in seen:
        seen.add(current)
        current = index.renames[current]
        if current in index.by_display:
            return list(index.by_display[current])
        if current in index.by_last:
            return list(index.by_last[current])
    return []


def module_path(module: str) -> str:
    """The repository path of a module such as SquigglyLine.Theorem.Defs."""
    return "lean/" + module.replace(".", "/") + ".lean"


def compute_import_closures(files: dict[str, SourceFile]) -> None:
    """For each file, the paths of itself and of every file it imports, directly or not."""
    for source in files.values():
        seen = {source.path}
        pending = [source.path]
        while pending:
            current = files.get(pending.pop())
            if current is None:
                continue
            for module in current.imports:
                path = module_path(module)
                if path not in seen:
                    seen.add(path)
                    pending.append(path)
        source.closure = seen


def build_index(include_tests: bool = False) -> Index:
    """Parse the sources and work out the cross references."""
    files: dict[str, SourceFile] = {}
    declarations: list[Declaration] = []
    for path in lean_paths(include_tests):
        source = parse_source_file(path)
        files[source.path] = source
        for declaration in source.declarations:
            declaration.identifier = len(declarations)
            declarations.append(declaration)
    by_display: dict[str, list[Declaration]] = defaultdict(list)
    by_qualified: dict[str, list[Declaration]] = defaultdict(list)
    by_last: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        by_display[declaration.display].append(declaration)
        by_qualified[declaration.qualified].append(declaration)
        if "." in declaration.display:
            by_last[declaration.display.rsplit(".", 1)[-1]].append(declaration)
    index = Index(files, declarations, by_display, by_qualified, by_last, read_renames(), 0)
    compute_import_closures(files)
    for declaration in declarations:
        allowed = declaration.file.closure if declaration.file else set()
        declaration.mentions = find_references(
            index, declaration.masked_statement, declaration.namespaces, declaration.identifier, allowed
        )
        declaration.uses = find_references(
            index, declaration.masked_proof, declaration.namespaces, declaration.identifier, allowed
        )
    for declaration in declarations:
        for other in declaration.mentions:
            declarations[other].mentioned_by.add(declaration.identifier)
        for other in declaration.uses:
            declarations[other].used_by.add(declaration.identifier)
    for old, new in index.renames.items():
        if old not in index.by_display:
            for declaration in follow_rename(index, old):
                declaration.renamed_from.append(old)
    index.text_files_read = collect_text_mentions(index)
    for declaration in declarations:
        declaration.text_mentions.sort(key=lambda mention: (mention.path, mention.line))
        declaration.renamed_from.sort()
    return index


_INDEX_CACHE: dict[bool, Index] = {}


def cached_index(include_tests: bool) -> Index:
    """Build the index once per process (the self-test calls many sub-commands)."""
    if include_tests not in _INDEX_CACHE:
        _INDEX_CACHE[include_tests] = build_index(include_tests)
    return _INDEX_CACHE[include_tests]


# --------------------------------------------------------------------------
# Words, stems and ranking
# --------------------------------------------------------------------------

STOP_WORDS = {"a", "an", "the", "of", "is", "are", "to", "in", "and", "or", "for", "by", "at", "on", "with", "it", "be"}
CAMEL_BOUNDARY = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
LETTER_RUN = re.compile(r"[A-Za-z]+")

FIELD_WEIGHTS = {
    "name": 10.0,
    "old_name": 4.0,
    "doc": 4.0,
    "section": 3.0,
    "statement": 2.0,
    "summary": 1.5,
    "proof": 1.0,
}


def stem(word: str) -> str:
    """A light stemmer: tokens and token, averages and average, share and shares."""
    word = word.lower()
    if word.endswith("ies") and len(word) > 4:
        return word[:-3] + "y"
    if not word.endswith("ss"):
        for suffix in ("ing", "ed", "es", "s"):
            if word.endswith(suffix) and len(word) - len(suffix) >= 3:
                word = word[:-len(suffix)]
                break
    if word.endswith("e") and len(word) > 3:
        word = word[:-1]
    return word


def split_words(text: str) -> list[str]:
    """Lower-case stems of the words of a text; snake_case and CamelCase are split."""
    spaced = CAMEL_BOUNDARY.sub(" ", text)
    return [stem(word) for word in LETTER_RUN.findall(spaced) if len(word) >= 2]


@dataclasses.dataclass
class Hit:
    declaration: Declaration
    score: float
    matched: int
    note: str = ""


def declaration_fields(declaration: Declaration, with_proofs: bool) -> dict[str, set[str]]:
    """The searchable word sets of a declaration, by field."""
    fields = {
        "name": set(split_words(declaration.display)),
        "old_name": set(split_words(" ".join(declaration.renamed_from))),
        "doc": set(split_words(declaration.doc)),
        "section": set(split_words(declaration.section)),
        "statement": set(split_words(declaration.statement)),
        "summary": set(split_words(declaration.file.header if declaration.file else "")),
    }
    if with_proofs:
        fields["proof"] = set(split_words(declaration.proof))
    return fields


def filter_declarations(index: Index, args: argparse.Namespace) -> list[Declaration]:
    """Apply --kind, --folder and --statement."""
    chosen = list(index.declarations)
    kind = getattr(args, "kind", None)
    if kind:
        allowed = KIND_GROUPS.get(kind, (kind,))
        chosen = [declaration for declaration in chosen if declaration.kind in allowed]
    folder = getattr(args, "folder", None)
    if folder:
        wanted = folder.strip("/").lower()
        chosen = [
            declaration for declaration in chosen
            if declaration.folder.lower() == wanted or declaration.folder.lower().startswith(wanted + "/")
        ]
    pattern = getattr(args, "statement", None)
    if pattern:
        compiled = re.compile(pattern)
        chosen = [declaration for declaration in chosen if compiled.search(declaration.statement)]
    return chosen


def rank_declarations(
    index: Index, declarations: list[Declaration], words: list[str], raw_words: list[str], with_proofs: bool
) -> list[Hit]:
    """Score every declaration against the query stems; best first."""
    stems = []
    for word in words:
        if word not in stems:
            stems.append(word)
    joined = "_".join(raw_words).lower()
    hits: list[Hit] = []
    for declaration in declarations:
        score = 0.0
        matched = 0
        fields = declaration_fields(declaration, with_proofs)
        for query_stem in stems:
            word_score = sum(
                FIELD_WEIGHTS[field] for field, vocabulary in fields.items() if query_stem in vocabulary
            )
            if word_score > 0:
                matched += 1
                score += word_score
        if matched == 0:
            continue
        if joined and joined == declaration.display.lower():
            score += 100.0
        note = ""
        if any(word in fields["old_name"] and word not in fields["name"] for word in stems):
            note = "renamed from " + ", ".join(declaration.renamed_from[:2])
        hits.append(Hit(declaration, score, matched, note))
    hits.sort(key=lambda hit: (-hit.matched, -hit.score, hit.declaration.display))
    return hits


# --------------------------------------------------------------------------
# Finding one declaration by name
# --------------------------------------------------------------------------


def find_declarations(index: Index, query: str) -> tuple[list[Declaration], str]:
    """Resolve a name: exact, old name, last part, or a unique prefix.

    Returns the declarations and a note on how the name was matched; more
    than one declaration means the name is ambiguous.
    """
    query = query.strip().strip("`")
    if query.startswith(ROOT_NAMESPACE + "."):
        query = query[len(ROOT_NAMESPACE) + 1:]
    if query in index.by_display:
        return list(index.by_display[query]), "exact"
    renamed = follow_rename(index, query)
    if renamed:
        return renamed, f"renamed from {query}"
    if query in index.by_last:
        return list(index.by_last[query]), "last part of a dotted name"
    prefixed = sorted(name for name in index.by_display if name.startswith(query))
    if prefixed:
        found = [declaration for name in prefixed for declaration in index.by_display[name]]
        return found, "prefix"
    lowered = query.lower()
    folded = sorted(name for name in index.by_display if name.lower() == lowered)
    if folded:
        return [declaration for name in folded for declaration in index.by_display[name]], "case ignored"
    return [], "none"


def suggest_names(index: Index, words: list[str]) -> list[str]:
    """Close names for a query that matched nothing."""
    vocabulary: set[str] = set()
    for name in index.by_display:
        vocabulary.update(part.lower() for part in re.split(r"[_.]", name) if part)
    suggestions: list[str] = []
    for word in words:
        for close in difflib.get_close_matches(word.lower(), sorted(vocabulary), n=3, cutoff=0.7):
            if close not in suggestions:
                suggestions.append(close)
    joined = "_".join(words)
    for close in difflib.get_close_matches(joined, sorted(index.by_display), n=3, cutoff=0.6):
        if close not in suggestions:
            suggestions.append(close)
    return suggestions


# --------------------------------------------------------------------------
# Output: one payload per command, printed as YAML (default) or JSON
# --------------------------------------------------------------------------

LINK = re.compile(r"\[([^\]]*)\]\([^)]*\)")


def truncate(text: str, limit: int) -> str:
    """Cut a text at a word boundary, closing no backtick left open."""
    if len(text) <= limit:
        return text
    cut = text[:limit].rsplit(" ", 1)[0].rstrip(",;:")
    if cut.count("`") % 2 == 1:
        cut = cut[:cut.rfind("`")].rstrip(" ,;:")
    return cut + " ..."


def first_sentence(doc: str, limit: int = 140) -> str:
    """The first sentence of a doc comment, on one line."""
    first_paragraph = doc.strip().split("\n\n")[0]
    text = LINK.sub(r"\1", " ".join(first_paragraph.split())).replace("**", "")
    in_code = False
    for position, character in enumerate(text):
        if character == "`":
            in_code = not in_code
        elif character in ".?!" and not in_code:
            following = text[position + 1:position + 3]
            if position + 1 == len(text) or (following[:1] == " " and not following[1:2].islower()):
                return truncate(text[:position + 1], limit)
    return truncate(text, limit)


def location(declaration: Declaration) -> str:
    return f"{declaration.path}:{declaration.line}"


def chapters_text(mentions: list[Mention]) -> str:
    chapters = sorted({mention.chapter for mention in mentions if mention.chapter is not None})
    return ", ".join(str(chapter) for chapter in chapters)


def brief_record(declaration: Declaration) -> dict:
    return {
        "name": declaration.display,
        "qualified": declaration.qualified,
        "kind": declaration.kind,
        "path": declaration.path,
        "line": declaration.line,
        "end_line": declaration.end_line,
        "doc_first_sentence": first_sentence(declaration.doc),
    }


def mention_records(declaration: Declaration) -> list[dict]:
    return [
        {"path": mention.path, "line": mention.line, "chapter": mention.chapter}
        for mention in declaration.text_mentions
    ]


def full_record(index: Index, declaration: Declaration, with_proof: bool) -> dict:
    record = brief_record(declaration)
    others = index.declarations
    record.update({
        "modifiers": declaration.modifiers,
        "attributes": declaration.attributes,
        "doc": declaration.doc,
        "section": declaration.section,
        "file_summary": declaration.file.title if declaration.file else "",
        "statement": declaration.statement,
        "proof": declaration.proof if with_proof else None,
        "proof_lines": declaration.proof_lines,
        "renamed_from": declaration.renamed_from,
        "uses": [brief_record(others[i]) for i in sorted(declaration.uses)],
        "mentions": [brief_record(others[i]) for i in sorted(declaration.mentions)],
        "used_by": [brief_record(others[i]) for i in sorted(declaration.used_by)],
        "mentioned_by": [brief_record(others[i]) for i in sorted(declaration.mentioned_by)],
        "used_by_count": len(declaration.used_by | declaration.mentioned_by),
        "text_mentions": mention_records(declaration),
    })
    return record


def print_json(payload: object) -> None:
    print(json.dumps(payload, ensure_ascii=False, indent=2))


# ---- a small YAML writer and reader (the subset the tool uses) -----------

BLOCK_KEYS = {"statement", "proof", "body", "header"}
FIRST_CHARACTERS_NEEDING_QUOTES = set(",[]{}#&*!|>'\"%@`")
WORDS_NEEDING_QUOTES = {"~", "null", "true", "false", "yes", "no", "on", "off", "y", "n", "=", "<<"}
NUMBER_LIKE = re.compile(
    r"^[-+]?(?:\d[\d_]*(?:\.\d*)?(?:e[-+]?\d+)?|\.\d+(?:e[-+]?\d+)?|0[xob][0-9a-f_]+|\.(?:inf|nan)"
    r"|\d+(?::[0-5]?\d)+(?:\.\d*)?)$",
    re.IGNORECASE,
)
DATE_LIKE = re.compile(r"^\d{4}-\d\d?-\d\d?")


def has_unsafe_character(text: str) -> bool:
    """A character that only a double-quoted (escaped) scalar can carry."""
    for character in text:
        code = ord(character)
        if (code < 32 and character not in "\n\t") or 0x7F <= code <= 0x9F:
            return True
        if character in "  ﻿":
            return True
    return False


def needs_quotes(text: str) -> bool:
    """Whether a one-line string would read back as something else if left plain."""
    if text != text.strip() or "\t" in text:
        return True
    if text.lower() in WORDS_NEEDING_QUOTES:
        return True
    if text[0] in FIRST_CHARACTERS_NEEDING_QUOTES:
        return True
    if text[0] in "-?:" and (len(text) == 1 or text[1] == " "):
        return True
    if text.startswith(("---", "...")):
        return True
    if ": " in text or " #" in text or text.endswith(":"):
        return True
    return bool(NUMBER_LIKE.match(text) or DATE_LIKE.match(text))


def yaml_scalar(value: object) -> str:
    """One value on one line: plain when safe, else single-quoted."""
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, (int, float)):
        return repr(value)
    text = str(value)
    if text == "":
        return "''"
    if "\n" in text or "\r" in text or has_unsafe_character(text):
        return json.dumps(text, ensure_ascii=False)
    if needs_quotes(text):
        return "'" + text.replace("'", "''") + "'"
    return text


def can_be_block(text: str) -> bool:
    return not (text.endswith("\n") or "\r" in text or has_unsafe_character(text))


def yaml_entry(key: str, value: object, indent: int, block_keys: set[str]) -> list[str]:
    """The lines of one `key: value` entry of a mapping whose keys sit at `indent`."""
    pad = " " * indent
    key_text = yaml_scalar(key)
    if isinstance(value, str) and (key in block_keys or "\n" in value) and can_be_block(value) and value != "":
        lines = value.split("\n")
        indicator = "2" if lines[0] == "" or lines[0].startswith(" ") else ""
        out = [f"{pad}{key_text}: |{indicator}-"]
        out += [(pad + "  " + line) if line else "" for line in lines]
        return out
    if isinstance(value, dict):
        if not value:
            return [f"{pad}{key_text}: {{}}"]
        return [f"{pad}{key_text}:"] + yaml_lines(value, indent + 2)
    if isinstance(value, list):
        if not value:
            return [f"{pad}{key_text}: []"]
        return [f"{pad}{key_text}:"] + yaml_lines(value, indent + 2)
    return [f"{pad}{key_text}: {yaml_scalar(value)}"]


def yaml_lines(value: object, indent: int = 0) -> list[str]:
    """Block-style YAML lines for a mapping or a list at the given column."""
    pad = " " * indent
    if isinstance(value, dict):
        if not value:
            return [pad + "{}"]
        block_keys = set(BLOCK_KEYS)
        if "statement" in value:
            block_keys.add("doc")
        lines: list[str] = []
        for key, item in value.items():
            lines += yaml_entry(str(key), item, indent, block_keys)
        return lines
    if isinstance(value, list):
        lines = []
        for item in value:
            if isinstance(item, dict) and item:
                inner = yaml_lines(item, indent + 2)
                inner[0] = pad + "- " + inner[0][indent + 2:]
                lines += inner
            elif isinstance(item, (dict, list)):
                if item:
                    raise TypeError("a list inside a list is not supported")
                lines.append(pad + "- " + ("{}" if isinstance(item, dict) else "[]"))
            else:
                lines.append(pad + "- " + yaml_scalar(item))
        return lines
    return [pad + yaml_scalar(value)]


def split_key(text: str) -> tuple[str, str] | None:
    """Split `key: rest` (or `key:`) of a mapping line; None when it is not one."""
    if text.startswith("'"):
        end = 1
        while end < len(text):
            if text[end] == "'":
                if text[end + 1:end + 2] == "'":
                    end += 2
                    continue
                break
            end += 1
        key = text[1:end].replace("''", "'")
        rest = text[end + 1:]
        if rest == ":" or rest.startswith(": "):
            return key, rest[1:].strip()
        return None
    if text.startswith('"'):
        match = re.match(r'("(?:\\.|[^"\\])*")(:(?: |$).*)$', text)
        if match:
            return json.loads(match.group(1)), match.group(2)[1:].strip()
        return None
    if text.endswith(":"):
        return text[:-1], ""
    position = text.find(": ")
    if position < 0:
        return None
    return text[:position], text[position + 2:].strip()


def read_scalar(text: str) -> object:
    if text.startswith("'") and text.endswith("'") and len(text) >= 2:
        return text[1:-1].replace("''", "'")
    if text.startswith('"'):
        return json.loads(text)
    if text == "[]":
        return []
    if text == "{}":
        return {}
    if text in ("null", "~", ""):
        return None
    if text == "true":
        return True
    if text == "false":
        return False
    if re.fullmatch(r"-?\d+", text):
        return int(text)
    return text


class YamlReader:
    """Reads back the YAML that `yaml_lines` writes (block mappings and lists,
    plain, single- and double-quoted scalars, `[]`, `{}` and `|` block scalars)."""

    def __init__(self, text: str) -> None:
        self.lines = text.split("\n")
        while self.lines and self.lines[-1] == "":
            self.lines.pop()
        self.position = 0

    def indent_of(self, line: str) -> int:
        return len(line) - len(line.lstrip(" "))

    def read(self) -> object:
        if not self.lines:
            return None
        return self.read_node(self.indent_of(self.lines[0]))

    def read_node(self, indent: int) -> object:
        line = self.lines[self.position]
        text = line[indent:]
        if text == "-" or text.startswith("- "):
            return self.read_list(indent)
        if split_key(text) is None:
            self.position += 1
            return read_scalar(text)
        return self.read_mapping(indent)

    def read_mapping(self, indent: int) -> dict:
        result: dict = {}
        while self.position < len(self.lines):
            line = self.lines[self.position]
            if line == "" or self.indent_of(line) != indent or line[indent:].startswith("- "):
                break
            key, rest = split_key(line[indent:])
            self.position += 1
            result[key] = self.read_value(indent, rest)
        return result

    def read_list(self, indent: int) -> list:
        result: list = []
        while self.position < len(self.lines):
            line = self.lines[self.position]
            if line == "" or self.indent_of(line) != indent or not (line[indent:] == "-" or line[indent:].startswith("- ")):
                break
            rest = line[indent + 2:]
            if rest != "" and split_key(rest) is not None:
                self.lines[self.position] = " " * (indent + 2) + rest
                result.append(self.read_mapping(indent + 2))
            else:
                self.position += 1
                result.append(read_scalar(rest) if rest else self.read_nested(indent))
        return result

    def read_nested(self, indent: int) -> object:
        if self.position < len(self.lines) and self.indent_of(self.lines[self.position]) > indent:
            return self.read_node(self.indent_of(self.lines[self.position]))
        return None

    def read_value(self, indent: int, rest: str) -> object:
        if rest.startswith("|"):
            return self.read_block(indent, rest)
        if rest == "":
            if self.position < len(self.lines):
                next_line = self.lines[self.position]
                next_indent = self.indent_of(next_line)
                if next_indent > indent or (next_indent == indent and next_line[indent:].startswith("- ")):
                    return self.read_node(next_indent)
            return None
        return read_scalar(rest)

    def read_block(self, indent: int, header: str) -> str:
        digits = re.search(r"\d", header)
        collected: list[str] = []
        while self.position < len(self.lines):
            line = self.lines[self.position]
            if line != "" and self.indent_of(line) <= indent:
                break
            collected.append(line)
            self.position += 1
        if digits:
            content_indent = indent + int(digits.group())
        else:
            first = next((line for line in collected if line.strip()), "")
            content_indent = self.indent_of(first)
        body = [line[content_indent:] if line else "" for line in collected]
        while body and body[-1] == "" and "+" not in header:
            body.pop()
        text = "\n".join(body)
        if "-" not in header:
            text += "\n"
        return text


def read_yaml(text: str) -> tuple[object, str]:
    """Read YAML text with PyYAML when it is installed, else with the small reader.
    Returns the data and the name of the reader used."""
    try:
        import yaml  # type: ignore
    except ImportError:
        return YamlReader(text).read(), "own reader"
    return yaml.safe_load(text), "PyYAML"


def prune(value: object) -> object:
    """Drop keys whose value is empty or null, at every depth."""
    if isinstance(value, dict):
        kept = {}
        for key, item in value.items():
            item = prune(item)
            if item is None or item == "" or item == [] or item == {}:
                continue
            kept[key] = item
        return kept
    if isinstance(value, list):
        return [prune(item) for item in value if item is not None]
    return value


RECORD_DROPPED_KEYS = {
    "name", "kind", "path", "line", "qualified", "end_line", "doc_first_sentence",
    "score", "matched_words", "note",
}
MENTIONS_SHOWN = 8


def compact(value: object, word_count: int, with_path: bool = True) -> object:
    """The short form of a payload for YAML: a record is `name`, `at`, `doc`, and
    `kind` when it is not a theorem."""
    if isinstance(value, list):
        return [compact(item, word_count, with_path) for item in value]
    if not isinstance(value, dict):
        return value
    if set(value) == {"path", "line", "chapter"}:
        return f"{value['path']}:{value['line']}"
    if {"name", "kind", "path", "line"} <= set(value):
        is_full = "statement" in value
        result: dict = {"name": value["name"]}
        if is_full or value["kind"] != "theorem":
            result["kind"] = value["kind"]  # in a list of hits, no kind means a theorem
        if with_path:
            result["at"] = f"{value['path']}:{value['line']}"
        else:
            result["line"] = value["line"]
        if not is_full:
            result["doc"] = value.get("doc_first_sentence", "")
        note = value.get("note", "")
        if note.startswith("renamed from "):
            result["renamed_from"] = note[len("renamed from "):]
        matched = value.get("matched_words")
        if matched is not None and word_count > 1 and matched < word_count:
            result["matched"] = f"{matched} of {word_count} words"
        is_definition = value["kind"] in DEFINITION_KINDS
        for key, item in value.items():
            if key in RECORD_DROPPED_KEYS:
                continue
            if is_definition and key == "proof":
                key = "body"
            elif is_definition and key == "proof_lines":
                key = "body_lines"
            result[key] = compact(item, word_count, with_path)
        return result
    return {key: compact(item, word_count, with_path) for key, item in value.items()}


def first_paragraphs(header: str) -> str:
    paragraphs = header.split("\n\n")
    return "\n".join("\n\n".join(paragraphs[:2]).split("\n")[:14])


def yaml_view(args: argparse.Namespace, payload: dict) -> dict:
    """The data the default (YAML) output prints, made from the --json payload."""
    word_count = payload.get("word_count") or 0
    command = args.command
    view = compact(payload, word_count, with_path=command != "file")
    assert isinstance(view, dict)
    limit = getattr(args, "limit", 10)
    if "suggestions" in view:
        view["close_names"] = view.pop("suggestions")
    if command == "search":
        for key in ("query", "word_count"):
            view.pop(key, None)
        total = view.pop("total", 0)
        more = total - len(view.get("hits", []))
        if more > 0:
            view["more"] = more
    if command in ("show", "define"):
        if view.get("matched_by") == "exact":
            view.pop("matched_by")
        if not getattr(args, "uses", False):
            view.pop("uses", None)
            view.pop("mentions", None)
        if not getattr(args, "used_by", False):
            view.pop("used_by", None)
            view.pop("mentioned_by", None)
        mentions = view.get("text_mentions", [])
        if len(mentions) > MENTIONS_SHOWN:
            view["text_mentions"] = mentions[:MENTIONS_SHOWN]
            view["text_mentions_more"] = len(mentions) - MENTIONS_SHOWN
    if command == "define":
        if not args.proof and view.get("body_lines", 0) > 15:
            view.pop("body", None)
        theorems = view.get("theorems_mentioning_it", [])
        if len(theorems) > limit:
            view["theorems_mentioning_it"] = theorems[:limit]
            view["theorems_mentioning_it_more"] = len(theorems) - limit
    if command == "file" and not args.full and "header" in view:
        view["header"] = first_paragraphs(view["header"])
    if command == "selftest":
        for check in view.get("checks", []):
            if check.get("ok") is True:
                check.pop("ok")
    if command == "stats":
        for key in ("theorems_without_doc_comment", "theorems_unused_and_unmentioned"):
            items = view.get(key, [])
            view[f"{key}_count"] = len(items)
            if len(items) > limit:
                view[key] = items[:limit]
    pruned = prune(view)
    assert isinstance(pruned, dict)
    return pruned


def emit(args: argparse.Namespace, payload: dict) -> None:
    """Print a payload as JSON (--json) or as YAML."""
    if args.json:
        print_json(payload)
    else:
        print("\n".join(yaml_lines(yaml_view(args, payload))))


# --------------------------------------------------------------------------
# Sub-commands
# --------------------------------------------------------------------------


def command_search(index: Index, args: argparse.Namespace) -> int:
    chosen = filter_declarations(index, args)
    raw_words = list(args.words)
    words = [stem(word) for raw in raw_words for word in LETTER_RUN.findall(CAMEL_BOUNDARY.sub(" ", raw))
             if len(word) >= 2 and word.lower() not in STOP_WORDS]
    if raw_words and not words:
        print("error: no usable words in the query", file=sys.stderr)
        return 2
    if not raw_words and not args.statement:
        print("error: give words, or --statement REGEX", file=sys.stderr)
        return 2
    distinct = len(set(words))

    if words:
        hits = rank_declarations(index, chosen, words, raw_words, args.in_proofs)
        for raw in raw_words:
            current = [] if raw in index.by_display else follow_rename(index, raw)
            for declaration in current:
                if declaration not in chosen:
                    continue
                existing = [hit for hit in hits if hit.declaration is declaration]
                if existing:
                    existing[0].score += 1000.0
                    existing[0].note = f"renamed from {raw}"
                else:
                    hits.append(Hit(declaration, 1000.0, distinct, f"renamed from {raw}"))
            if current:
                hits.sort(key=lambda hit: (-hit.matched, -hit.score, hit.declaration.display))
    else:
        hits = [Hit(declaration, 0.0, 0) for declaration in chosen]
        hits.sort(key=lambda hit: hit.declaration.display)

    shown = hits[:args.limit]
    payload: dict = {}
    if words and hits and distinct > 1 and hits[0].matched < distinct:
        payload["note"] = f"no declaration matches all {distinct} words; best partial matches follow"
    if not hits:
        payload["error"] = "no match for: " + " ".join(raw_words)
    payload["query"] = raw_words
    payload["word_count"] = distinct
    payload["total"] = len(hits)
    payload["hits"] = [
        dict(brief_record(hit.declaration), score=round(hit.score, 2), matched_words=hit.matched, note=hit.note)
        for hit in shown
    ]
    payload["suggestions"] = [] if hits else suggest_names(index, raw_words)
    emit(args, payload)
    return 0 if hits else 1


def resolve_one(index: Index, query: str, restrict_to_definitions: bool) -> tuple[Declaration | None, str, list[Declaration]]:
    """Resolve a name to one declaration. Returns (found, note, candidates)."""
    candidates, note = find_declarations(index, query)
    if restrict_to_definitions:
        candidates = [declaration for declaration in candidates if declaration.is_definition]
    if len(candidates) == 1:
        return candidates[0], note, candidates
    return None, note, candidates


def report_unresolved(index: Index, args: argparse.Namespace, query: str, candidates: list[Declaration]) -> int:
    payload: dict = {}
    if candidates:
        payload["error"] = f"{query} is ambiguous: {len(candidates)} candidates"
    else:
        payload["error"] = f"no declaration named {query}"
    payload["query"] = query
    payload["candidates"] = [brief_record(declaration) for declaration in candidates[:20]]
    if len(candidates) > 20:
        payload["more_candidates"] = len(candidates) - 20
    payload["suggestions"] = [] if candidates else suggest_names(index, [query])
    emit(args, payload)
    return 1


def command_show(index: Index, args: argparse.Namespace) -> int:
    declaration, note, candidates = resolve_one(index, args.name, False)
    if declaration is None:
        return report_unresolved(index, args, args.name, candidates)
    record = full_record(index, declaration, args.proof)
    record["matched_by"] = note
    emit(args, record)
    return 0


def command_define(index: Index, args: argparse.Namespace) -> int:
    declaration, note, candidates = resolve_one(index, args.name, True)
    if declaration is None:
        if not candidates:
            others, _ = find_declarations(index, args.name)
            if others:
                emit(args, {
                    "error": f"{args.name} is a theorem, not a definition",
                    "use": f"show {args.name}",
                })
                return 1
        return report_unresolved(index, args, args.name, candidates)
    theorems = [
        other for other in sorted((index.declarations[i] for i in declaration.mentioned_by),
                                  key=lambda d: (d.path, d.line))
        if other.is_theorem
    ]
    record = full_record(index, declaration, True)
    record["matched_by"] = note
    record["theorems_mentioning_it"] = [brief_record(other) for other in theorems]
    emit(args, record)
    return 0


def find_file(index: Index, query: str) -> list[SourceFile]:
    """Resolve a path, a path ending, or a file name without .lean."""
    wanted = query.replace("\\", "/").strip("/")
    lowered = wanted.lower()
    if lowered.endswith(".lean"):
        lowered = lowered[:-len(".lean")]
    exact = [source for path, source in index.files.items() if path.lower() == wanted.lower()]
    if exact:
        return exact
    ends = [
        source for path, source in index.files.items()
        if path.lower()[:-len(".lean")].endswith("/" + lowered) or path.lower()[:-len(".lean")] == lowered
    ]
    return sorted(ends, key=lambda source: source.path)


def command_file(index: Index, args: argparse.Namespace) -> int:
    matches = find_file(index, args.path)
    if len(matches) != 1:
        payload: dict = {"error": f"no file matches {args.path}" if not matches else f"{args.path} is ambiguous"}
        payload["query"] = args.path
        payload["candidates"] = [source.path for source in matches]
        payload["suggestions"] = [] if matches else difflib.get_close_matches(args.path, sorted(index.files), n=3, cutoff=0.4)
        emit(args, payload)
        return 1
    source = matches[0]
    counts: dict[str, int] = defaultdict(int)
    for declaration in source.declarations:
        counts[declaration.kind] += 1
    emit(args, {
        "path": source.path,
        "folder": source.folder,
        "title": source.title,
        "header": source.header,
        "counts": dict(counts),
        "declarations": [brief_record(declaration) for declaration in source.declarations],
    })
    return 0


def command_chapter(index: Index, args: argparse.Namespace) -> int:
    in_chapter = [
        declaration for declaration in index.declarations
        if any(mention.chapter == args.number for mention in declaration.text_mentions)
    ]
    if not in_chapter:
        emit(args, {"error": f"no Lean name is mentioned in book chapter {args.number}", "chapter": args.number})
        return 1
    chapter_files = sorted({
        mention.path for declaration in in_chapter for mention in declaration.text_mentions
        if mention.chapter == args.number
    })
    emit(args, {
        "chapter": args.number,
        "files": chapter_files,
        "names": [
            dict(brief_record(declaration), lines=[
                mention.line for mention in declaration.text_mentions if mention.chapter == args.number
            ])
            for declaration in sorted(in_chapter, key=lambda d: (d.path, d.line))
        ],
    })
    return 0


def is_unused(declaration: Declaration) -> bool:
    return not declaration.used_by and not declaration.mentioned_by and not declaration.text_mentions


def command_stats(index: Index, args: argparse.Namespace) -> int:
    table: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    for declaration in index.declarations:
        table[declaration.folder or "(root)"][declaration.kind] += 1
    undocumented = [d for d in index.declarations if d.is_theorem and not d.doc]
    unused = [d for d in index.declarations if d.is_theorem and is_unused(d)]
    totals: dict[str, int] = defaultdict(int)
    for declaration in index.declarations:
        totals[declaration.kind] += 1
    emit(args, {
        "files": len(index.files),
        "declarations": len(index.declarations),
        "by_kind": dict(sorted(totals.items())),
        "by_folder": {folder: dict(sorted(kinds.items())) for folder, kinds in sorted(table.items())},
        "theorems_without_doc_comment": [brief_record(d) for d in undocumented],
        "theorems_unused_and_unmentioned": [brief_record(d) for d in unused],
    })
    return 0


# --------------------------------------------------------------------------
# The generated page docs/theorem-index.md
# --------------------------------------------------------------------------

FOLDER_ORDER = ["Theorem", "Networks", "Connections", "Supporting"]


def folder_sort_key(folder: str) -> tuple[int, str]:
    top = folder.split("/")[0]
    rank = FOLDER_ORDER.index(top) if top in FOLDER_ORDER else len(FOLDER_ORDER)
    if folder == "":
        rank = -1
    return rank, folder


def page_sentence(declaration: Declaration, limit: int = 100) -> str:
    sentence = first_sentence(declaration.doc, limit)
    return sentence if sentence else "(no doc comment)"


def link_to(source_path: str) -> str:
    return "../" + source_path


def render_index_page(index: Index) -> str:
    """The text of docs/theorem-index.md. Deterministic: no dates, no absolute paths."""
    definitions = [d for d in index.declarations if d.is_definition and not d.name.startswith("instance@")]
    theorems = [d for d in index.declarations if d.is_theorem]
    out: list[str] = []
    out.append("# Theorem index")
    out.append("")
    out.append("This page is written by `python scripts/find_theorem.py index --write`. Do not edit it by")
    out.append("hand. `python scripts/find_theorem.py index --check` fails when it is out of date.")
    out.append("")
    out.append(f"It lists {len(theorems)} theorems and {len(definitions)} definitions of the Lean library.")
    out.append("")
    out.append("## How to look something up")
    out.append("")
    out.append("The page is long. To ask a question, use the tool, or grep this page.")
    out.append("")
    out.append("```bash")
    out.append("python scripts/find_theorem.py search share token")
    out.append("python scripts/find_theorem.py show every_token_gets_a_share --proof --used-by")
    out.append("python scripts/find_theorem.py define COVERS_WITHIN")
    out.append("python scripts/find_theorem.py search --statement LipschitzWith --kind theorem --limit 5")
    out.append("python scripts/find_theorem.py file AttentionRate")
    out.append("python scripts/find_theorem.py chapter 36")
    out.append("```")
    out.append("")
    out.append("The output is YAML, without the keys that are empty. Add `--json` for JSON with every key.")
    out.append("`search` ranks by name, doc comment, section heading and statement. `show` prints the")
    out.append("statement, where it is quoted and what uses it. An old name from")
    out.append("[RENAMES-theorems.txt](../lean/RENAMES-theorems.txt) finds the new one.")
    out.append("`python scripts/find_theorem.py --help` has more examples.")
    out.append("")
    out.append("## What this does not do")
    out.append("")
    out.append("- It does not know Mathlib. Only names declared under `lean/SquigglyLine` are here.")
    out.append("- Cross references are by name. A name used only through `open`, an alias, a macro or a")
    out.append("  structure projection may be missed. A name inside a comment is not a use.")
    out.append("  A name counts as used only if its file is the same file or one it imports.")
    out.append("- A book chapter is listed for a name when the chapter writes the whole name.")
    out.append("- A statement is cut at the first `:=` that no `let` used up; an unusual shape may be cut wrongly.")
    out.append("")
    out.append("## Definitions")
    out.append("")
    out.append("Every definition, abbreviation, structure and class, by name. Each line: the name, what")
    out.append("its doc comment says first, and the file (under `lean/SquigglyLine/`).")
    out.append("")
    for declaration in sorted(definitions, key=lambda d: (d.display.lower(), d.display, d.path, d.line)):
        short_path = declaration.path[len("lean/SquigglyLine/"):] if declaration.path.startswith("lean/SquigglyLine/") else declaration.path
        out.append(f"- `{declaration.display}`: {page_sentence(declaration, 70)} `{short_path}`")
    out.append("")
    out.append("## Theorems")
    out.append("")
    out.append("By folder and file, in the order of the file. The numbers are the book chapters that")
    out.append("write the name.")
    folders: dict[str, list[SourceFile]] = defaultdict(list)
    for source in index.files.values():
        if any(d.is_theorem for d in source.declarations):
            folders[source.folder].append(source)
    for folder in sorted(folders, key=folder_sort_key):
        out.append("")
        out.append(f"### {folder if folder else '(root)'}")
        for source in sorted(folders[folder], key=lambda s: s.path):
            out.append("")
            title = truncate(first_sentence(source.title, 100), 100)
            file_name = source.path.rsplit("/", 1)[-1]
            out.append(f"#### [{file_name}]({link_to(source.path)})" + (f": {title}" if title else ""))
            out.append("")
            for declaration in source.declarations:
                if not declaration.is_theorem:
                    continue
                chapters = chapters_text(declaration.text_mentions)
                tail = f" (ch {chapters})" if chapters else ""
                out.append(f"- `{declaration.display}`: {page_sentence(declaration)}{tail}")
    out.append("")
    return "\n".join(out)


def command_index(index: Index, args: argparse.Namespace) -> int:
    page = render_index_page(index)
    name = INDEX_PAGE.relative_to(ROOT).as_posix()
    if args.write:
        INDEX_PAGE.write_text(page, encoding="utf-8", newline="\n")
        emit(args, {"wrote": name, "lines": page.count("\n")})
        return 0
    if args.check:
        current = INDEX_PAGE.read_bytes().decode("utf-8").replace("\r\n", "\n") if INDEX_PAGE.exists() else None
        if current == page:
            emit(args, {"up_to_date": name})
            return 0
        emit(args, {"error": f"{name} is out of date", "fix": "python scripts/find_theorem.py index --write"})
        return 1
    print("error: give --write or --check", file=sys.stderr)
    return 2


# --------------------------------------------------------------------------
# The self-test
# --------------------------------------------------------------------------

INDEPENDENT_THEOREM = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)?(?:theorem|lemma)\s", re.MULTILINE)
INDEPENDENT_DEFINITION = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s", re.MULTILINE
)
INDEPENDENT_OTHER = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:structure|class|instance|inductive)\b",
    re.MULTILINE,
)
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)


def independent_counts(include_tests: bool) -> dict[str, int]:
    """Count declarations with plain regexes, without using the parser."""
    counts = {"theorem": 0, "definition": 0, "other": 0}
    for path in lean_paths(include_tests):
        text = BLOCK_COMMENT.sub("", path.read_text(encoding="utf-8"))
        counts["theorem"] += len(INDEPENDENT_THEOREM.findall(text))
        counts["definition"] += len(INDEPENDENT_DEFINITION.findall(text))
        counts["other"] += len(INDEPENDENT_OTHER.findall(text))
    return counts


def run_main_quietly(arguments: list[str]) -> tuple[int, str]:
    """Run a sub-command in this process, return (exit code, its output)."""
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(io.StringIO()):
        code = main(arguments)
    return code, buffer.getvalue()


def declared_in_sources(name: str, sources: str) -> bool:
    """Whether a name is declared, by a plain regex over the raw sources."""
    last = re.escape(name.rsplit(".", 1)[-1])
    pattern = r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|class)\s+(?:[\w.]*\.)?" + last + r"(?![\w'])"
    return re.search(pattern, sources, flags=re.MULTILINE) is not None


def independent_closures() -> dict[str, set[str]]:
    """Import closures worked out again from the raw sources, apart from the parser."""
    direct: dict[str, set[str]] = {}
    for path in lean_paths(False):
        relative = path.relative_to(ROOT).as_posix()
        text = BLOCK_COMMENT.sub("", path.read_text(encoding="utf-8"))
        direct[relative] = {
            module_path(module) for module in re.findall(r"^import\s+(SquigglyLine[\w.]*)", text, flags=re.MULTILINE)
        }
    closures: dict[str, set[str]] = {}
    for start in direct:
        seen = {start}
        stack = [start]
        while stack:
            for target in direct.get(stack.pop(), set()):
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        closures[start] = seen
    return closures


def yaml_round_trip_checks(record) -> None:
    """Check that the YAML of four commands reads back as the data --json gives."""
    commands = [
        ["search", "share", "token"],
        ["show", "depth_merges_the_tokens_at_a_geometric_rate", "--proof", "--uses", "--used-by"],
        ["define", "COVERS_WITHIN"],
        ["chapter", "49"],
    ]
    for command in commands:
        parsed = build_parser().parse_args(command)
        json_code, json_text = run_main_quietly(command + ["--json"])
        yaml_code, yaml_text = run_main_quietly(command)
        expected = yaml_view(parsed, json.loads(json_text))
        label = " ".join(command)
        own = YamlReader(yaml_text).read()
        record(json_code == yaml_code and own == expected, f"YAML of `{label}` reads back equal to the --json data",
               f"empty keys dropped; own reader; exit {yaml_code}; {len(yaml_text)} characters")
        data, reader = read_yaml(yaml_text)
        if reader != "own reader":
            record(data == expected, f"YAML of `{label}` reads back equal with {reader}", "")


def selftest(index: Index) -> int:
    results: list[dict] = []

    def record(passed: bool, name: str, detail: str) -> None:
        results.append({"name": name, "ok": passed, "detail": detail})

    theorems = [d for d in index.declarations if d.is_theorem]
    expected = independent_counts(False)
    record(len(theorems) == expected["theorem"], "theorem count equals a regex count",
           f"parser {len(theorems)}, regex {expected['theorem']}")
    definitions = [d for d in index.declarations if d.kind in ("def", "abbrev")]
    record(len(definitions) == expected["definition"], "def and abbrev count equals a regex count",
           f"parser {len(definitions)}, regex {expected['definition']}")
    others = [d for d in index.declarations if d.kind in ("structure", "class", "instance", "inductive")]
    record(len(others) == expected["other"], "structure, class and instance count equals a regex count",
           f"parser {len(others)}, regex {expected['other']}")

    all_sources = "\n".join(
        BLOCK_COMMENT.sub("", path.read_text(encoding="utf-8")) for path in lean_paths(False)
    )
    surviving = [(old, new) for old, new in index.renames.items() if declared_in_sources(new, all_sources)]
    not_found = []
    for old, new in surviving:
        code, _ = run_main_quietly(["show", new, "--json"])
        if code != 0:
            not_found.append(new)
    record(not not_found, "every renamed theorem that still exists is found by show",
           f"{len(surviving)} of {len(index.renames)} new names exist; not found: {not_found[:3]}")

    unresolved = []
    checked = 0
    for old, new in surviving:
        if old in index.by_display:
            continue
        checked += 1
        found, _ = find_declarations(index, old)
        if not found or not any(new == d.display or new.rsplit(".", 1)[-1] == d.name.rsplit(".", 1)[-1] for d in found):
            unresolved.append(old)
    record(not unresolved, "every old name resolves to its new one",
           f"{checked} old names checked; unresolved: {unresolved[:3]}")
    old_sample = next((old for old, _ in surviving if old not in index.by_display), None)
    if old_sample:
        code, output = run_main_quietly(["search", old_sample])
        record(code == 0 and "renamed_from" in output, "search for an old name says renamed_from",
               f"{old_sample}: exit {code}")

    code, output = run_main_quietly(["search", "share", "token", "--limit", "3", "--json"])
    top = [hit["name"] for hit in json.loads(output)["hits"]] if code == 0 else []
    record("every_token_gets_a_share" in top, "search share token finds every_token_gets_a_share in the top 3",
           f"top 3: {top}")
    code, _ = run_main_quietly(["search", "qzxqzxqzx"])
    record(code == 1, "search for a nonsense word exits 1", f"exit {code}")
    code, _ = run_main_quietly(["search"])
    record(code == 2, "search with nothing to look for is a usage error", f"exit {code}")
    code, output = run_main_quietly(["search", "causal", "mask", "cache"])
    record(code == 0 and output.startswith("note: no declaration matches all"),
           "a partial match starts with a note and keeps exit 0", f"exit {code}")
    code, output = run_main_quietly(["search", "share", "token"])
    record('"' not in output, "the default output of search share token has no double quote character",
           f"{len(output)} characters")

    empty = [d.display for d in index.declarations if not d.statement.strip()]
    record(not empty, "no declaration has an empty statement", f"{len(empty)} empty: {empty[:3]}")
    leaking = [d.display for d in index.declarations if re.search(r":=\s*by\b", d.statement)]
    record(not leaking, "no statement contains `:= by`", f"{len(leaking)}: {leaking[:3]}")
    last_let = [
        d.display for d in index.declarations
        if d.statement.split("\n")[-1].strip().startswith("let ")
    ]
    record(not last_let, "no statement ends on a let line", f"{len(last_let)}: {last_let[:3]}")
    no_proof = [d.display for d in theorems if not d.proof]
    record(not no_proof, "every theorem has a proof", f"{len(no_proof)}: {no_proof[:3]}")

    closures = independent_closures()
    crossings = []
    references = 0
    for declaration in index.declarations:
        allowed = closures.get(declaration.path, {declaration.path})
        for other in declaration.uses | declaration.mentions:
            references += 1
            if index.declarations[other].path not in allowed:
                crossings.append(f"{declaration.display} -> {index.declarations[other].display}")
    record(not crossings, "no use or mention crosses a missing import",
           f"{references} references checked; crossings: {crossings[:3]}")

    for command in (["stats"], ["file", "Defs"], ["chapter", "4"], ["define", "COVERS_WITHIN"], ["show", "squiggly_line_theorem"]):
        code, output = run_main_quietly(command + ["--json"])
        try:
            json.loads(output)
            valid = True
        except ValueError:
            valid = False
        record(code == 0 and valid, f"{' '.join(command)} --json is valid JSON", f"exit {code}")

    yaml_round_trip_checks(record)

    first = render_index_page(index)
    second = render_index_page(index)
    record(first == second, "the index page is deterministic", f"{len(first)} characters")
    record(str(ROOT) not in first and str(ROOT).replace("\\", "/") not in first,
           "the index page has no absolute path", "")

    failed = sum(1 for result in results if not result["ok"])
    args = argparse.Namespace(json=False, command="selftest")
    payload = {"passed": len(results) - failed, "failed": failed, "checks": results}
    emit(args, payload)
    return 1 if failed else 0


# --------------------------------------------------------------------------
# The command line
# --------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--json", action="store_true", help="machine-readable output")
    common.add_argument("--include-tests", action="store_true", help="also index the Tests folder")

    parser = argparse.ArgumentParser(
        prog="find_theorem.py",
        description="Search the theorems, definitions and proofs of the Lean library.",
        epilog=EPILOG,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    commands = parser.add_subparsers(dest="command", required=True, metavar="COMMAND")

    search = commands.add_parser("search", parents=[common], help="ranked keyword search")
    search.add_argument("words", nargs="*", help="words; snake_case names are split into words")
    search.add_argument("--kind", help="theorem, def, abbrev, structure, class, instance")
    search.add_argument("--folder", help="Theorem, Networks, Supporting/Training, ...")
    search.add_argument("--statement", metavar="REGEX", help="keep declarations whose statement matches")
    search.add_argument("--in-proofs", action="store_true", help="also search the proof text")
    search.add_argument("--limit", type=int, default=10, help="hits to print (default 10)")

    show = commands.add_parser("show", parents=[common], help="one declaration: doc, statement, uses")
    show.add_argument("name", help="a name, a unique prefix, or an old name")
    show.add_argument("--proof", action="store_true", help="print the proof")
    show.add_argument("--uses", action="store_true", help="list what it uses and mentions")
    show.add_argument("--used-by", action="store_true", help="list what uses or mentions it")

    define = commands.add_parser("define", parents=[common], help="a definition and the theorems about it")
    define.add_argument("name")
    define.add_argument("--proof", action="store_true", help="print the whole body")
    define.add_argument("--uses", action="store_true")
    define.add_argument("--used-by", action="store_true")
    define.add_argument("--limit", type=int, default=15, help="theorems to list (default 15)")

    file_command = commands.add_parser("file", parents=[common], help="a file: header and one line per declaration")
    file_command.add_argument("path", help="a path, a path ending, or a file name such as AttentionRate")
    file_command.add_argument("--full", action="store_true", help="print the whole header")

    chapter = commands.add_parser("chapter", parents=[common], help="the Lean names a book chapter mentions")
    chapter.add_argument("number", type=int)

    stats = commands.add_parser("stats", parents=[common], help="counts and gaps")
    stats.add_argument("--limit", type=int, default=15, help="names to list per gap (default 15)")

    index_command = commands.add_parser("index", parents=[common], help="write or check docs/theorem-index.md")
    index_command.add_argument("--write", action="store_true")
    index_command.add_argument("--check", action="store_true")

    commands.add_parser("selftest", parents=[common], help="check the tool against the sources")
    return parser


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass
    parser = build_parser()
    try:
        args = parser.parse_args(argv)
    except SystemExit as exit_request:
        return exit_request.code if isinstance(exit_request.code, int) else 2
    if args.command == "index" and not (args.write or args.check):
        print("error: give --write or --check", file=sys.stderr)
        return 2
    index = cached_index(args.include_tests)
    if args.command == "selftest":
        return selftest(index)
    handlers = {
        "search": command_search,
        "show": command_show,
        "define": command_define,
        "file": command_file,
        "chapter": command_chapter,
        "stats": command_stats,
        "index": command_index,
    }
    return handlers[args.command](index, args)


if __name__ == "__main__":
    sys.exit(main())
