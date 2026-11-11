/- Erdős #982, n = 12: interface clauses `S12_4` after chunk 4 of 10 of the LRAT proof (the lemmas of chunks
1..4 that a later chunk uses), read from `lrat/n12/s4.cls` (SHA-256 ddee88f0f1c309b4e383bb7e19723681689c0de783b7185d663f3432f5ab1805), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_4 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s4.cls")

end E982C
