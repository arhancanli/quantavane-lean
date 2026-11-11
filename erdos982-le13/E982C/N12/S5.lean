/- Erdős #982, n = 12: interface clauses `S12_5` after chunk 5 of 10 of the LRAT proof (the lemmas of chunks
1..5 that a later chunk uses), read from `lrat/n12/s5.cls` (SHA-256 e350c08dad28f705c907d7d1d30e254f5fca19d41aec73c2f0f93131ad61ccd7), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_5 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s5.cls")

end E982C
