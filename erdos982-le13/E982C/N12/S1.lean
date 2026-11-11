/- Erdős #982, n = 12: interface clauses `S12_1` after chunk 1 of 10 of the LRAT proof (the lemmas of chunks
1..1 that a later chunk uses), read from `lrat/n12/s1.cls` (SHA-256 f944f2a6b865c2df60392348a6f6b13c3157ed442d9889080c77717c5f9372b2), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_1 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s1.cls")

end E982C
