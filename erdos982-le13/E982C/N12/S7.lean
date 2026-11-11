/- Erdős #982, n = 12: interface clauses `S12_7` after chunk 7 of 10 of the LRAT proof (the lemmas of chunks
1..7 that a later chunk uses), read from `lrat/n12/s7.cls` (SHA-256 ea84ab2a2a8af87aca41d04a5367fccfa1958b42a9fb3d9e42ede8060573b173), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_7 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s7.cls")

end E982C
