#!/bin/sh
# Regenerate lrat/gen_13_5.lrat (234 MB, not in git): dump gen 13 5, solve with the CaDiCaL shipped with Lean
# 4.33.1 (deterministic, about 65 s and 650 MB), trim to the lemmas reachable from the empty clause and renumber
# consecutively (Lean's checker appends clauses in order), then check the SHA-256 sums.
set -e
cd "$(dirname "$0")/.."
CAD=${CAD:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical}
TRIM=${TRIM:-./lrat/erdos982_lrat_trim}
[ -x "$TRIM" ] || cc -O2 -o "$TRIM" lrat/erdos982_lrat_trim.c
lake exe dumpc 13 5 lrat/gen_13_5.cnf
"$CAD" -q --lrat=true --binary=false lrat/gen_13_5.cnf lrat/gen_13_5.raw.lrat || true
"$TRIM" lrat/gen_13_5.raw.lrat lrat/gen_13_5.lrat 943423
shasum -a 256 lrat/gen_13_5.cnf lrat/gen_13_5.lrat
echo "expected: ed4e34de6feaed263dc5866b3af6c4e954247c5ccc58e9bd022e63b238f4cf3d  lrat/gen_13_5.cnf"
echo "expected: 1fcedc5bb418565f05a1bcb7c1926efcc935abca663f0aa74bed30ccfdf0973d  lrat/gen_13_5.lrat"
