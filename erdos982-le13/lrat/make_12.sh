#!/bin/zsh
# Regenerate the n = 12 LRAT data (about 2 GB, not in git): dump gen12 (= gen 12 5 plus the 24 cut clauses) from
# Lean, refute it with CaDiCaL 3.0.1 writing a binary LRAT (about 25 min and 450 MB on a loaded Mac; 1.41 GB proof),
# trim it to the lemmas reachable from the empty clause and cut it into 10 text chunks joined by interface clauses
# (erdos982_lrat_split), check every chunk with drat-trim's lrat-check and with lratcheck, regenerate the Lean
# modules E982C/N12/*.lean and Cert12.lean, and print the SHA-256 sums (compare with README.md).
# Optional: TRIM=1 also writes the whole trimmed proof n12/gen12_full.lrat and checks it with both checkers.
set -e
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/bin:$PATH
CAD=${CAD:-$HOME/qv-foundations-20261111/dl/cadical/src/build/cadical}
LC=${LC:-$HOME/qv-foundations-20261111/dl/drat-trim/src/lrat-check}
OC=${OC:-$HOME/qv-foundations-20261111/scripts/lratcheck}
mkdir -p lrat/n12
[ -x lrat/erdos982_lrat_split ] || cc -O2 -o lrat/erdos982_lrat_split lrat/erdos982_lrat_split.c
[ -x lrat/erdos982_lrat_trim_bin ] || cc -O2 -o lrat/erdos982_lrat_trim_bin lrat/erdos982_lrat_trim_bin.c
lake build dump12
.lake/build/bin/dump12 lrat/n12/gen12.cnf
"$CAD" -q --lrat=true --binary=true lrat/n12/gen12.cnf lrat/n12/gen12.lratb || true
if [ -n "$TRIM" ]; then
  lrat/erdos982_lrat_trim_bin lrat/n12/gen12.lratb lrat/n12/gen12_full.lrat 567771
  "$LC" lrat/n12/gen12.cnf lrat/n12/gen12_full.lrat | grep VERIFIED
  "$OC" lrat/n12/gen12.cnf lrat/n12/gen12_full.lrat | tail -1
fi
# m = 567771 clauses in gen12; selector variables start at atom 41484 (= lsTop of gen12, see Split.lean)
lrat/erdos982_lrat_split lrat/n12/gen12.lratb 567771 41484 10 lrat/n12 lrat/n12/gen12.cnf
for j in 1 2 3 4 5 6 7 8 9 10; do
  "$LC" lrat/n12/c$j.cnf lrat/n12/p$j.lrat | grep VERIFIED
  "$OC" lrat/n12/c$j.cnf lrat/n12/p$j.lrat | tail -1
done
rm -f lrat/n12/gen12.lratb
python3 -I lrat/make_n12_modules.py 10
shasum -a 256 lrat/n12/gen12.cnf lrat/n12/p*.lrat lrat/n12/s*.cls
