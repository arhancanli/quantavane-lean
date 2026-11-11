/- Erdős #982, n = 12: interface clauses `S12_9` after chunk 9 of 10 of the LRAT proof (the lemmas of chunks
1..9 that a later chunk uses), read from `lrat/n12/s9.cls` (SHA-256 a3a4d0b027c71e15cffddec62ae40f7cd5397f41c75d4d49795b090042349f00), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_9 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s9.cls")

end E982C
