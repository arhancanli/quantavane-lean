/- Erdős #982, n = 12: interface clauses `S12_3` after chunk 3 of 10 of the LRAT proof (the lemmas of chunks
1..3 that a later chunk uses), read from `lrat/n12/s3.cls` (SHA-256 87a74eb40e162406fbf925105549c68c13172bab6850a9060163eabde9b44360), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_3 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s3.cls")

end E982C
