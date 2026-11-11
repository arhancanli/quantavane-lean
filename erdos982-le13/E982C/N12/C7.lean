/- Erdős #982, n = 12, LRAT chunk 7 of 10: `gen12 ∧ S12_6 ∧ ¬S12_7` is unsatisfiable, so `gen12 ∧ S12_6 ⊨ S12_7`. The proof `lrat/n12/p7.lrat` (text LRAT, SHA-256
4c5486e7471c024c7138852ed3e255cd77911b4024ff6d59867bff6203785ad4, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 6 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C6
import E982C.N12.S6
import E982C.N12.S7

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_7 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p7.lrat")

theorem chunk12_7 : (chunkCNF gen12 S12_6 S12_7).Unsat := LRAT.check_sound P12_7 _ (by native_decide)

end E982C
