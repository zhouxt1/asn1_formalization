#!/usr/bin/env python3
"""The ASN.1 of a specification's PDF, from `pdftotext -layout` output: the text between
`-- ASN1START` and `-- ASN1STOP`, with what the PDF did to it undone.
  pdf_asn1.py SPEC.txt OUT.asn [HEADER-REGEX]
- page headers and footers (lines matching HEADER-REGEX, default ETSI's) are dropped;
- typographic characters are put back: … to ..., curly quotes to straight, dashes to hyphens;
- a name the line wrap broke after a hyphen is rejoined (X.680 12.2.1: no name ends with one);
- a comment that wrapped onto the next line, which starts at column 0, stays a comment."""
import re, sys
src, out = sys.argv[1], sys.argv[2]
hdr = re.compile(sys.argv[3] if len(sys.argv) > 3 else r'^(ETSI|\d+\s+ETSI TS .*|ETSI TS .*)$')
lines = open(src, encoding='utf-8', errors='replace').read().replace('\f', '\n').split('\n')
body, inb = [], False
for l in lines:
    if '-- ASN1START' in l: inb = True; continue
    if '-- ASN1STOP' in l: inb = False; body.append(''); continue
    if inb and not hdr.match(l.strip()): body.append(l)
s = '\n'.join(body)
for a, b in [('…', '...'), ('“', '"'), ('”', '"'), ('‘', "'"), ('’', "'"),
             ('–', '-'), ('—', '-'), (' ', ' ')]:
    s = s.replace(a, b)
s = re.sub(r'([A-Za-z0-9])-\n([A-Za-z0-9])', r'\1-\2', s)
res = []
for l in s.split('\n'):
    prev = res[-1] if res else ''
    pc = prev.find('--')
    if pc >= 0 and prev[pc+2:].find('--') < 0 and len(prev) >= 88 and l and not l[0].isspace() \
            and '::=' not in l and not l.startswith('--'):
        res.append('-- ' + l)
    else:
        res.append(l)
open(out, 'w').write('\n'.join(res))
