/- Erdős #982, n = 12, LRAT chunk 8 of 10: `gen12 ∧ S12_7 ∧ ¬S12_8` is unsatisfiable, so `gen12 ∧ S12_7 ⊨ S12_8`. The proof `lrat/n12/p8.lrat` (text LRAT, SHA-256
7d5d225b3ffe0fe58db499eeb72efa3b69c538360f6d98b7c6ace0176b9f9954, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 7 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C7
import E982C.N12.S7
import E982C.N12.S8

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_8 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p8.lrat")

theorem chunk12_8 : (chunkCNF gen12 S12_7 S12_8).Unsat := LRAT.check_sound P12_8 _ (by native_decide)

end E982C
