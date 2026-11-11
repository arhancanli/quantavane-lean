/- Erdős #982, n = 12, LRAT chunk 4 of 10: `gen12 ∧ S12_3 ∧ ¬S12_4` is unsatisfiable, so `gen12 ∧ S12_3 ⊨ S12_4`. The proof `lrat/n12/p4.lrat` (text LRAT, SHA-256
13dabd9cd54e87070f3448dd0bfb90935559195a2545cb937f7b3dcc7e0effa7, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 3 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C3
import E982C.N12.S3
import E982C.N12.S4

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_4 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p4.lrat")

theorem chunk12_4 : (chunkCNF gen12 S12_3 S12_4).Unsat := LRAT.check_sound P12_4 _ (by native_decide)

end E982C
