#!/usr/bin/env python3
"""Run asn1check resolve over each protocol directory of a corpus; one TSV row per directory.
Usage: corpus_run.py KIND ROOT OUT.tsv   (KIND: pycrate | dirs; $ASN1CHECK overrides the binary)"""
import sys, os, re, subprocess, pathlib
kind, root, out = sys.argv[1], pathlib.Path(sys.argv[2]), sys.argv[3]
EXE = os.environ.get('ASN1CHECK', str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/asn1check'))
EXT = ('.asn', '.asn1', '.ASN', '.ASN1')
units = []
for d in sorted(p for p in root.iterdir() if p.is_dir()):
    files = []
    lm = d / 'load_mod.txt'
    if kind == 'pycrate' and lm.exists():
        for l in lm.read_text(errors='replace').splitlines():
            l = l.strip()
            if l and not l.startswith('#') and (d / l).exists(): files.append(str(d / l))
    if not files:
        files = sorted(str(p) for p in d.rglob('*') if p.suffix in EXT and p.is_file())
    if files: units.append((d.name, files))
rows = []
for name, files in units:
    try:
        r = subprocess.run([EXE, 'resolve'] + files, capture_output=True, text=True, timeout=600)
        o = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        rows.append((name, len(files), 'TIMEOUT', '', '', '', '', '')); continue
    perr = re.search(r'^(\S+): ERROR (.*)$', o, re.M)
    if perr:
        rows.append((name, len(files), 'PARSE', '', '', '', '', f'{os.path.basename(perr.group(1))}: {perr.group(2)[:160]}'))
        continue
    def num(pat):
        m = re.search(pat, o, re.M); return m.group(1) if m else '?'
    unread = re.search(r'^unread: (\d+) values, (\d+) objects, (\d+) actual', o, re.M)
    first = ''
    for pat in [r'^validity rules broken: [1-9]\d*\n  (.*)$', r'^type references that do not resolve: [1-9]\d*\n  (.*)$', r'^diagnostics: [1-9]\d*\n  (.*)$']:
        m = re.search(pat, o, re.M)
        if m: first = m.group(1)[:160]; break
    rows.append((name, len(files), 'OK',
                 '/'.join(unread.groups()) if unread else '?',
                 num(r'^type references that do not resolve: (\d+)'),
                 num(r'^diagnostics: (\d+)'), num(r'^validity rules broken: (\d+)'), first))
with open(out, 'w') as f:
    f.write('unit\tfiles\tstatus\tunread(v/o/a)\tunresolved\tdiag\tbroken\tfirst\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
ok = sum(1 for r in rows if r[2]=='OK'); clean = sum(1 for r in rows if r[2]=='OK' and r[3]=='0/0/0' and r[4]=='0' and r[5]=='0' and r[6]=='0')
print(f'{len(rows)} units: {ok} parsed, {clean} clean, {len(rows)-ok} parse errors/timeouts')
