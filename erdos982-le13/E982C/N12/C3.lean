/- Erdős #982, n = 12, LRAT chunk 3 of 10: `gen12 ∧ S12_2 ∧ ¬S12_3` is unsatisfiable, so `gen12 ∧ S12_2 ⊨ S12_3`. The proof `lrat/n12/p3.lrat` (text LRAT, SHA-256
e5a4835dd0064e8630889c1551465ecd49e9f218a57b3387526ab1502496404b, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 2 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C2
import E982C.N12.S2
import E982C.N12.S3

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_3 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p3.lrat")

theorem chunk12_3 : (chunkCNF gen12 S12_2 S12_3).Unsat := LRAT.check_sound P12_3 _ (by native_decide)

end E982C
