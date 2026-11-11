/- Erdős #982, n = 12: interface clauses `S12_6` after chunk 6 of 10 of the LRAT proof (the lemmas of chunks
1..6 that a later chunk uses), read from `lrat/n12/s6.cls` (SHA-256 195efa2b3ac06b50f294e5117b9c2a1c0ba3a84be0509d6b8d420bdb53ef6e82), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_6 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s6.cls")

end E982C
