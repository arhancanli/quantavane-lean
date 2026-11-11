/-
Erdős #982, n = 12: the CNF `gen12` is `gen 12 5` followed by 24 cut clauses. Each cut clause says that five
equal-length relations `|p o p a| = |p o p b|` (listed as triples `(o, a, b)` in `cuts12`) do not all hold; the 24
relation lists are the images of one list under the dihedral group of the 12-gon (`Angle12.lean` proves each cut
clause true for every convex 12-gon, by angles). Std-only module (no Mathlib), like `Cnf.lean`.
-/
import E982C.Cnf

open Std.Sat

namespace E982C

/-- the 24 cut relation lists (from `cuts12_images.json`, in the order of the CNF given to the SAT solver) -/
def cuts12 : List (List (Fin 12 × Fin 12 × Fin 12)) := [
  [(8, 5, 6), (8, 10, 11), (10, 7, 8), (11, 4, 6), (11, 5, 8)],
  [(1, 4, 7), (1, 6, 8), (2, 4, 5), (4, 1, 2), (4, 6, 7)],
  [(0, 5, 7), (0, 6, 9), (9, 0, 11), (9, 6, 7), (11, 8, 9)],
  [(2, 5, 8), (2, 7, 9), (3, 5, 6), (5, 2, 3), (5, 7, 8)],
  [(0, 9, 10), (1, 6, 8), (1, 7, 10), (10, 0, 1), (10, 7, 8)],
  [(3, 6, 9), (3, 8, 10), (4, 6, 7), (6, 3, 4), (6, 8, 9)],
  [(1, 10, 11), (2, 7, 9), (2, 8, 11), (11, 1, 2), (11, 8, 9)],
  [(4, 7, 10), (4, 9, 11), (5, 7, 8), (7, 4, 5), (7, 9, 10)],
  [(0, 2, 3), (0, 9, 10), (2, 0, 11), (3, 0, 9), (3, 8, 10)],
  [(5, 0, 10), (5, 8, 11), (6, 8, 9), (8, 5, 6), (8, 10, 11)],
  [(1, 3, 4), (1, 10, 11), (3, 0, 1), (4, 1, 10), (4, 9, 11)],
  [(6, 0, 9), (6, 1, 11), (7, 9, 10), (9, 0, 11), (9, 6, 7)],
  [(2, 0, 11), (2, 4, 5), (4, 1, 2), (5, 0, 10), (5, 2, 11)],
  [(7, 0, 2), (7, 1, 10), (8, 10, 11), (10, 0, 1), (10, 7, 8)],
  [(3, 0, 1), (3, 5, 6), (5, 2, 3), (6, 0, 3), (6, 1, 11)],
  [(8, 1, 3), (8, 2, 11), (9, 0, 11), (11, 1, 2), (11, 8, 9)],
  [(4, 1, 2), (4, 6, 7), (6, 3, 4), (7, 0, 2), (7, 1, 4)],
  [(0, 2, 3), (0, 9, 10), (9, 0, 3), (9, 2, 4), (10, 0, 1)],
  [(5, 2, 3), (5, 7, 8), (7, 4, 5), (8, 1, 3), (8, 2, 5)],
  [(1, 3, 4), (1, 10, 11), (10, 1, 4), (10, 3, 5), (11, 1, 2)],
  [(6, 3, 4), (6, 8, 9), (8, 5, 6), (9, 2, 4), (9, 3, 6)],
  [(0, 2, 3), (2, 0, 11), (2, 4, 5), (11, 2, 5), (11, 4, 6)],
  [(7, 4, 5), (7, 9, 10), (9, 6, 7), (10, 3, 5), (10, 4, 7)],
  [(0, 3, 6), (0, 5, 7), (1, 3, 4), (3, 0, 1), (3, 5, 6)]]

/-- the cut clause of a relation list: not all of the equalities `|o a| = |o b|` hold -/
def cutClause {n : Nat} (R : List (Fin n × Fin n × Fin n)) : CNF.Clause (Atom n) :=
  R.map fun r => (Eq' (cp r.1 r.2.1) (cp r.1 r.2.2), false)

def genA12 : CNF (Atom 12) :=
  ⟨(eqvCls 12 ++ ordCls 12 ++ classCls 12 5 ++ sideCls 12 ++ acuteCls 12 ++ cuts12.map cutClause).toArray⟩

def gen12 : CNF Nat := genA12.relabel enc

end E982C
