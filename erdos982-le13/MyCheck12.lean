import E982C.Main12
import FormalConjectures.ErdosProblems.«982»
/-! Erdős #982: our theorems inhabit formal-conjectures' own statement at n = 12 and at every 3 ≤ n ≤ 13, and the
axioms they rely on. -/
example : type_of% (Erdos982.erdos_982 12 (by norm_num)) := E982C.erdos_982_twelve
example (n : ℕ) (hn : 3 ≤ n) (h13 : n ≤ 13) : type_of% (Erdos982.erdos_982 n hn) :=
  E982C.erdos_982_le_thirteen n hn h13
#print axioms E982C.erdos_982_twelve
#print axioms E982C.erdos_982_le_thirteen
