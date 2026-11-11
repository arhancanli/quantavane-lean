/- Erdős #982, n = 12: interface clauses `S12_2` after chunk 2 of 10 of the LRAT proof (the lemmas of chunks
1..2 that a later chunk uses), read from `lrat/n12/s2.cls` (SHA-256 9b0b3d92765e8308d45831e7a2a035341d11cef79d92539bece79a7e0ab8cbab), written by `lrat/erdos982_lrat_split`.
Any list is sound here: see `E982C.Split`. -/
import E982C.Split

open Std.Sat

namespace E982C

def S12_2 : List (CNF.Clause Nat) := parseCls (include_str "../../lrat/n12/s2.cls")

end E982C
