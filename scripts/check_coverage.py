#!/usr/bin/env python3
"""Check a coverage map: every backticked Lean name it cites exists, every ledger id is in OPEN.md,
every file exists, and every Status is one of the allowed values. Usage: scripts/check_coverage.py COVERAGE.md"""
import re, sys, pathlib, collections

root = pathlib.Path(__file__).resolve().parent.parent
src = '\n'.join(p.read_text() for p in list(root.glob('Asn1/**/*.lean')) + list(root.glob('Tests/*.lean')))
opn = (root / 'OPEN.md').read_text()
ledger = set(re.findall(r'\| ((?:X68[0-3]|X69[01])-\d+) \|', opn))
statuses = {'mechanized', 'partial', 'notation', 'n/a', 'open', 'informative'}

# names defined anywhere: def/inductive/structure/abbrev/theorem/instance, constructors, fields
defined = set(re.findall(r'^\s*(?:private |protected |noncomputable )*(?:def|inductive|structure|abbrev|theorem|lemma|instance|class)\s+([\w.\']+)', src, re.M))
defined |= set(re.findall(r'^\s*\|\s*([\w\']+)', src, re.M))          # constructors
defined |= set(re.findall(r'^\s+([\w\']+)\s*:', src, re.M))            # structure fields / binders
short = {d.split('.')[-1] for d in defined}

bad, rows, counts = [], 0, collections.Counter()
for path in sys.argv[1:]:
    lines = pathlib.Path(path).read_text().splitlines()
    start = next((i for i, l in enumerate(lines) if l.strip() == '## The map'), -1) + 1
    for ln, line in enumerate(lines, 1):
        if ln <= start:
            continue
        if not line.startswith('|') or line.startswith('|---') or line.startswith('| Clause'):
            continue
        cells = [c.strip() for c in line.strip('|').split('|')]
        if len(cells) < 4:
            bad.append(f'{path}:{ln}: fewer than 4 cells'); continue
        rows += 1
        st = cells[2].split()[0] if cells[2] else ''
        counts[st] += 1
        if st not in statuses:
            bad.append(f'{path}:{ln}: status {cells[2]!r}')
        for lid in re.findall(r'(?:X68[0-3]|X69[01])-\d+', line):
            if lid not in ledger:
                bad.append(f'{path}:{ln}: ledger id {lid} not in OPEN.md')
        for tok in re.findall(r'`([^`]+)`', cells[3]):
            t = tok.strip()
            if '/' in t or t.endswith('.lean') or t.endswith('.md'):
                f = t.split(':')[0]
                if not ((root / f).exists() or (root / 'Asn1' / f).exists() or (root / 'Asn1/X680' / f).exists() or (root / 'Tests' / f).exists()):
                    bad.append(f'{path}:{ln}: file {t} not found')
                continue
            for part in re.split(r'[\s,()]+', t):
                part = part.strip('.')
                if not part or not re.match(r'^[A-Za-z_][\w.\']*$', part):
                    continue
                last = part.split('.')[-1]
                if last in ('X680', 'X690', 'X691', 'Asn1') or part in defined or last in short:
                    continue
                if re.search(r'\b' + re.escape(last) + r'\b', src):
                    continue
                bad.append(f'{path}:{ln}: Lean name `{part}` not found')
print(f'{rows} rows', dict(counts))
print('\n'.join(bad) if bad else 'all citations check out')
sys.exit(1 if bad else 0)
