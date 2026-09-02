#!/usr/bin/env bash
# Regenerate the figures in effort/README.md.
#
# Lean-side token and time figures come from the Claude Code session transcripts.
# The ChatGPT-side token figures are not recoverable locally; see effort/README.md section 1.
set -euo pipefail
cd "$(dirname "$0")/.."

SESSIONS="${CLAUDE_SESSIONS:-$HOME/.claude/projects/-Users-aaron-Downloads-Bescovitchs-1-2}"
PIVOT="${PIVOT:-2026-09-02T05:41:44}"   # the turn the Gram-certificate document arrived

echo "════ Lean formalization: tokens and wall clock"
if [ -d "$SESSIONS" ]; then
  python3 - "$SESSIONS" "$PIVOT" <<'PY'
import sys, json, glob, os
from datetime import datetime as D
base, pivot = sys.argv[1], sys.argv[2]
paths = glob.glob(os.path.join(base, '*.jsonl')) + \
        glob.glob(os.path.join(base, '*', 'subagents', '**', '*.jsonl'), recursive=True)
def tally(lo, hi):
    n = i = o = cw = cr = 0; first = last = None
    for p in paths:
        try: fh = open(p, encoding='utf-8')
        except OSError: continue
        for line in fh:
            try: d = json.loads(line)
            except ValueError: continue
            t = d.get('timestamp') or ''
            if (lo and t < lo) or (hi and t >= hi): continue
            m = d.get('message')
            if isinstance(m, dict) and isinstance(m.get('usage'), dict):
                u = m['usage']; n += 1
                i  += u.get('input_tokens', 0) or 0
                o  += u.get('output_tokens', 0) or 0
                cw += u.get('cache_creation_input_tokens', 0) or 0
                cr += u.get('cache_read_input_tokens', 0) or 0
                if t:
                    first = t if not first or t < first else first
                    last  = t if not last  or t > last  else last
    return n, i, o, cw, cr, first, last
for label, lo, hi in (("Phase 1  Bernstein (abandoned)", None, pivot),
                      ("Phase 2  Gram (delivered)",      pivot, None)):
    n, i, o, cw, cr, f, l = tally(lo, hi)
    if not f: print(f"  {label}: no records"); continue
    dur = D.fromisoformat(l[:19]) - D.fromisoformat(f[:19])
    print(f"  {label}")
    print(f"    wall clock  {f[:19]} -> {l[:19]}  ({dur})")
    print(f"    api calls   {n:,}")
    print(f"    output      {o:,}   input {i:,}")
    print(f"    cache       write {cw:,}   read {cr:,}")
    print(f"    in+out+cw   {i+o+cw:,}")
PY
else
  echo "  session transcripts not found at $SESSIONS"
fi

echo
echo "════ Lines of Lean"
python3 - <<'PY'
import os, collections
tot, files = collections.Counter(), collections.Counter()
grand = grandf = code = 0
for dp, dn, fn in os.walk('.'):
    if '.lake' in dp or '.git' in dp: continue
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f)
        n = sum(1 for _ in open(p, encoding='utf-8'))
        c = sum(1 for l in open(p, encoding='utf-8')
                if l.strip() and not l.strip().startswith('--'))
        parts = p.split(os.sep)
        area = parts[2] if len(parts) > 3 and parts[1] == 'Besicovitch' else 'root'
        if f in ('Solution.lean', 'Challenge.lean', 'Besicovitch.lean'): area = 'root'
        tot[area] += n; files[area] += 1; grand += n; grandf += 1; code += c
for a, n in tot.most_common():
    print(f"  {a:<22}{files[a]:>4} files {n:>8,} lines")
print(f"  {'TOTAL':<22}{grandf:>4} files {grand:>8,} lines   ({code:,} non-blank non-comment)")
PY

echo
echo "════ Repository history"
echo "  commits            $(git rev-list --count HEAD)"
echo "  first              $(git log --reverse --format='%ai' | head -1)"
echo "  latest             $(git log -1 --format='%ai')"

echo
echo "════ Machine verification cost (re-measure with a cold build)"
echo "  rm -rf .lake/build/lib/lean/Besicovitch && time lake build Solution Challenge"
