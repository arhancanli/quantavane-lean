/- Erdős #982, n = 12, LRAT chunk 1 of 10: `gen12 ∧ ¬S12_1` is unsatisfiable, so `gen12 ⊨ S12_1`. The proof `lrat/n12/p1.lrat` (text LRAT, SHA-256
e91045cedef81e96336688a9752095c3b586e5d2a21258e8cf72f1a3e1343ad4, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. -/
import E982C.Cnf12
import E982C.N12.S1

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_1 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p1.lrat")

theorem chunk12_1 : (chunkCNF gen12 [] S12_1).Unsat := LRAT.check_sound P12_1 _ (by native_decide)

end E982C
