/- Erdős #982, n = 12, LRAT chunk 2 of 10: `gen12 ∧ S12_1 ∧ ¬S12_2` is unsatisfiable, so `gen12 ∧ S12_1 ⊨ S12_2`. The proof `lrat/n12/p2.lrat` (text LRAT, SHA-256
4efb04d8be257672ea62d219926cb6cb468e0232d8c1a6cd9d980a5696bfb55e, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 1 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C1
import E982C.N12.S1
import E982C.N12.S2

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_2 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p2.lrat")

theorem chunk12_2 : (chunkCNF gen12 S12_1 S12_2).Unsat := LRAT.check_sound P12_2 _ (by native_decide)

end E982C
