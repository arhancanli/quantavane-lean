/- Erdős #982, n = 12, LRAT chunk 10 of 10: `gen12 ∧ S12_9` is unsatisfiable. The proof `lrat/n12/p10.lrat` (text LRAT, SHA-256
28bb666700559e9bd8deda074a2ae2a7a3b7e1cbced66dded659d62761e3913c, from `lrat/erdos982_lrat_split`) is checked by Lean's verified LRAT checker evaluated by
`native_decide`. It imports chunk 9 only so that Lake builds the chunks one at a time. -/
import E982C.Cnf12
import E982C.N12.C9
import E982C.N12.S9

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def P12_10 : Array LRAT.IntAction := parseProof' (include_str "../../lrat/n12/p10.lrat")

theorem chunk12_10 : (lastCNF gen12 S12_9).Unsat := LRAT.check_sound P12_10 _ (by native_decide)

end E982C
