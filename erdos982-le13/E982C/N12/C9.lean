/- Erdős #982, n = 12, LRAT chunk 9 of 10: `gen12 ∧ S12_8 ∧ ¬S12_9` is unsatisfiable, so `gen12 ∧ S12_8 ⊨ S12_9`. The proof `lrat/n12/p9.lrat` (text LRAT, SHA-256
496b999f8224a486eb8c14270597de9668756dd1e51168cf9e3d7703c55332d4, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 8 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C8
import E982C.N12.S8
import E982C.N12.S9

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_9 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p9.lrat")

theorem chunk12_9 : (chunkCNF gen12 S12_8 S12_9).Unsat := LRAT.check_sound P12_9 _ (by native_decide)

end E982C
