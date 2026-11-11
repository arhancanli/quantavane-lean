import E982C.Main
import E982C.Main13
import FormalConjectures.ErdosProblems.«982»
/-! Coordinator's own check (11 Nov 2026): our theorems inhabit formal-conjectures' own statement of Erdős #982 at
n = 10, 11 and 13, and the axioms they rely on. -/
example : type_of% (Erdos982.erdos_982 10 (by norm_num)) := E982C.erdos_982_ten
example : type_of% (Erdos982.erdos_982 11 (by norm_num)) := E982C.erdos_982_eleven
example : type_of% (Erdos982.erdos_982 13 (by norm_num)) := E982C.erdos_982_thirteen
#print axioms E982C.erdos_982_ten
#print axioms E982C.erdos_982_eleven
#print axioms E982C.erdos_982_thirteen
#print axioms E982C.erdos_982_le_eleven
#print axioms E982C.erdos_982_le_thirteen_ne_twelve
