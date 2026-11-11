/- Erdős #982, n = 12: interface clauses `S12_8` after chunk 8 of 10 of the LRAT proof (the lemmas of chunks
1..8 that a later chunk uses), read from `lrat/n12/s8.cls` (SHA-256 8bf8273dffb2c900dc57455e2cbdc2554ce41763dbe6fd81c316d5ee041544d7), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_8 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s8.cls")

end E982C
