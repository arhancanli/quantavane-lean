# Write the Lean modules for the chunked n = 12 LRAT check: E982C/N12/S<j>.lean (interface clauses), C<j>.lean (one
# native_decide LRAT check per chunk, chained by imports so that Lake builds them one at a time) and E982C/Cert12.lean
# (gen12_unsat). Each module records the SHA-256 of the data file it reads with include_str: Lake does not track
# include_str inputs, so regenerating the data must change the .lean source to force a rebuild.
# Usage (from the project root): python3 -I lrat/make_n12_modules.py K
import hashlib, os, sys
K = int(sys.argv[1])
D = 'E982C/N12'
os.makedirs(D, exist_ok=True)
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 24), b''): h.update(b)
    return h.hexdigest()
for j in range(1, K):
    f = f'lrat/n12/s{j}.cls'
    open(f'{D}/S{j}.lean', 'w').write(f'''/- Erdős #982, n = 12: interface clauses `S12_{j}` after chunk {j} of {K} of the LRAT proof (the lemmas of chunks
1..{j} that a later chunk uses), read from `{f}` (SHA-256 {sha(f)}), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_{j} : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s{j}.cls")

end E982C
''')
for j in range(1, K + 1):
    f = f'lrat/n12/p{j}.lrat'
    imps = ['E982C.Cnf12']
    if j > 1: imps += [f'E982C.N12.C{j-1}', f'E982C.N12.S{j-1}']
    if j < K: imps.append(f'E982C.N12.S{j}')
    if j < K:
        stmt = f'(chunkCNF gen12 {"[]" if j == 1 else f"S12_{j-1}"} S12_{j}).Unsat'
        what = (f'`gen12 ∧ {"" if j == 1 else f"S12_{j-1} ∧ "}¬S12_{j}` is unsatisfiable, so '
                f'`gen12{"" if j == 1 else f" ∧ S12_{j-1}"} ⊨ S12_{j}`')
    else:
        stmt = f'(lastCNF gen12 S12_{K-1}).Unsat'
        what = f'`gen12 ∧ S12_{K-1}` is unsatisfiable'
    chain = '' if j == 1 else f' It imports chunk {j-1} only so that Lake builds the chunks one at a time.'
    open(f'{D}/C{j}.lean', 'w').write(f'''/- Erdős #982, n = 12, LRAT chunk {j} of {K}: {what}. The proof `{f}` (text LRAT, SHA-256
{sha(f)}, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`.{chain} -/
''' + ''.join(f'import {x}\n' for x in imps) + f'''
open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_{j} : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p{j}.lrat")

theorem chunk12_{j} : {stmt} := LRAT.check_sound P12_{j} _ (by native_decide)

end E982C
''')
steps = '\n'.join(f'{"  · " if j == 1 else "    "}have h{j} := chunk_sound _ _ _ chunk12_{j} a hF {"(by simp)" if j == 1 else f"h{j-1}"}'
                  for j in range(1, K))
open('E982C/Cert12.lean', 'w').write(f'''/-
Erdős #982, n = 12: `gen12` (`gen 12 5` plus the 24 cut clauses) is unsatisfiable. LRAT certificate: CaDiCaL 3.0.1
(`--lrat=true --binary=true`, 1,355 s), trimmed to the 2,505,174 lemmas reachable from the empty clause and cut into
{K} chunks of about {2039 // K} MB of text (`lrat/erdos982_lrat_split`). Each chunk is checked by Lean's verified LRAT
checker (`E982C.N12.C1` ... `C{K}`, one `native_decide` each), and the chunks are joined by `chunk_sound` and
`last_sound` (`E982C.Split`).
-/
import E982C.N12.C{K}

open Std.Sat

namespace E982C

theorem gen12_unsat : gen12.Unsat := by
  intro a
  cases hF : gen12.eval a
  · rfl
{steps}
    exact (last_sound _ _ chunk12_{K} a hF h{K-1}).elim

end E982C
''')
print('wrote', K, 'chunk modules')
