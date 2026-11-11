/- Erdős #982, n = 12, LRAT chunk 6 of 10: `gen12 ∧ S12_5 ∧ ¬S12_6` is unsatisfiable, so `gen12 ∧ S12_5 ⊨ S12_6`. The proof `lrat/n12/p6.lrat` (text LRAT, SHA-256
0c6fb1e99587685fa52bfd3e057da87e348cb1b07eb1b662aa3cec2d37c454ce, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 5 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C5
import E982C.N12.S5
import E982C.N12.S6

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_6 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p6.lrat")

theorem chunk12_6 : (chunkCNF gen12 S12_5 S12_6).Unsat := LRAT.check_sound P12_6 _ (by native_decide)

end E982C
