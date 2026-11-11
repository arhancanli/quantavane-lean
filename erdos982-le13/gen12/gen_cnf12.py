import json
import os
HERE=os.path.dirname(os.path.abspath(__file__))
E12=HERE+'/'
imgs=json.load(open(E12+'cuts12_images.json'))
def rl(R): return '[' + ', '.join(f'({o}, {p}, {q})' for _,o,p,q in R) + ']'
lines=',\n  '.join(rl(R) for R in imgs)
out=f'''/-
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
  {lines}]

/-- the cut clause of a relation list: not all of the equalities `|o a| = |o b|` hold -/
def cutClause {{n : Nat}} (R : List (Fin n × Fin n × Fin n)) : CNF.Clause (Atom n) :=
  R.map fun r => (Eq' (cp r.1 r.2.1) (cp r.1 r.2.2), false)

def genA12 : CNF (Atom 12) :=
  ⟨(eqvCls 12 ++ ordCls 12 ++ classCls 12 5 ++ sideCls 12 ++ acuteCls 12 ++ cuts12.map cutClause).toArray⟩

def gen12 : CNF Nat := genA12.relabel enc

end E982C
'''
open(HERE+'/../E982C/Cnf12.lean','w').write(out)
print(len(imgs))
