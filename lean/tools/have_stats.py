"""List the `have` statements of the Lean sources, to decide which to promote to lemmas.

    cd lean
    PYTHONIOENCODING=utf-8 python tools/have_stats.py SquigglyLine

Prints how many `have`s there are, how long their proofs are, which statements
repeat, and the longest blocks. The size of a block is measured by indentation
and a repeat by the statement text, so the numbers are approximate. The rule
for promoting a `have` is in `STYLE.md`, under "When a `have` becomes a lemma".
"""
import re, sys, collections, pathlib

root = pathlib.Path(sys.argv[1])
have_re = re.compile(r'^(\s*)have\b(.*)$')
records = []  # (file, line_no, indent, header_text, length_in_lines)

for path in root.rglob('*.lean'):
    lines = path.read_text(encoding='utf-8', errors='replace').splitlines()
    for i, line in enumerate(lines):
        m = have_re.match(line)
        if not m:
            continue
        indent = len(m.group(1))
        # the have "block": following lines that are indented deeper than the have line
        j = i + 1
        while j < len(lines) and (lines[j].strip() == '' or len(lines[j]) - len(lines[j].lstrip()) > indent):
            j += 1
        length = j - i
        header = re.sub(r'\s+', ' ', m.group(2)).strip()
        records.append((str(path.relative_to(root)), i + 1, indent, header, length))

total = len(records)
one_liners = sum(1 for r in records if r[4] == 1)
short = sum(1 for r in records if r[4] <= 3)
long_ = sum(1 for r in records if r[4] >= 8)
print('total have:', total)
print('one-line have:', one_liners, f'({100*one_liners/total:.0f}%)')
print('<=3 lines:', short, f'({100*short/total:.0f}%)')
print('>=8 lines:', long_, f'({100*long_/total:.0f}%)')

# reuse: identical statement (text up to ':=') appearing more than once
def statement(header):
    h = header.split(':=')[0]
    # drop the name
    h = re.sub(r'^\S+\s*:\s*', '', h) if ':' in h else h
    return h.strip()

counts = collections.Counter(statement(r[3]) for r in records if ':' in r[3])
dups = {k: v for k, v in counts.items() if v > 1 and len(k) > 12}
print('distinct statements appearing 2+ times:', len(dups))
print('have occurrences that repeat another statement:', sum(v for v in dups.values()))
for k, v in sorted(dups.items(), key=lambda kv: -kv[1])[:8]:
    print(f'  x{v}: {k[:110]}')

# per-theorem size: have lines vs total
big = sorted(records, key=lambda r: -r[4])[:5]
print('longest have blocks:')
for r in big:
    print(f'  {r[0]}:{r[1]} ({r[4]} lines) {r[3][:80]}')
