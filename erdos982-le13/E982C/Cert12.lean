/-
Erdős #982, n = 12: `gen12` (`gen 12 5` plus the 24 cut clauses) is unsatisfiable. LRAT certificate: CaDiCaL 3.0.1
(`--lrat=true --binary=true`, 1,355 s), trimmed to the 2,505,174 lemmas reachable from the empty clause and cut into
10 chunks of about 203 MB of text (`lrat/erdos982_lrat_split`). Each chunk is checked by Lean's verified LRAT
checker (`E982C.N12.C1` ... `C10`, one `native_decide` each), and the chunks are joined by `chunk_sound` and
`last_sound` (`E982C.Split`).
-/
import E982C.N12.C10

open Std.Sat

namespace E982C

theorem gen12_unsat : gen12.Unsat := by
  intro a
  cases hF : gen12.eval a
  · rfl
  · have h1 := chunk_sound _ _ _ chunk12_1 a hF (by simp)
    have h2 := chunk_sound _ _ _ chunk12_2 a hF h1
    have h3 := chunk_sound _ _ _ chunk12_3 a hF h2
    have h4 := chunk_sound _ _ _ chunk12_4 a hF h3
    have h5 := chunk_sound _ _ _ chunk12_5 a hF h4
    have h6 := chunk_sound _ _ _ chunk12_6 a hF h5
    have h7 := chunk_sound _ _ _ chunk12_7 a hF h6
    have h8 := chunk_sound _ _ _ chunk12_8 a hF h7
    have h9 := chunk_sound _ _ _ chunk12_9 a hF h8
    exact (last_sound _ _ chunk12_10 a hF h9).elim

end E982C
