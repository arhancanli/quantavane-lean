/- Erdős #982, n = 12, LRAT chunk 5 of 10: `gen12 ∧ S12_4 ∧ ¬S12_5` is unsatisfiable, so `gen12 ∧ S12_4 ⊨ S12_5`. The proof `lrat/n12/p5.lrat` (text LRAT, SHA-256
e8b5e08507a9f84c81dd99915d2bb049417f75643f22530ffb5c8113421b8181, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 4 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C4
import E982C.N12.S4
import E982C.N12.S5

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_5 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p5.lrat")

theorem chunk12_5 : (chunkCNF gen12 S12_4 S12_5).Unsat := LRAT.check_sound P12_5 _ (by native_decide)

end E982C
