import E982C.Main12
import FormalConjectures.ErdosProblems.«982»
/-- The type of formal-conjectures' `Erdos982.erdos_982 12 _` is inhabited by our theorem. -/
example : type_of% (Erdos982.erdos_982 12 (by norm_num)) := E982C.erdos_982_twelve
/-- and every case 3 ≤ n ≤ 13. -/
example (n : ℕ) (hn : 3 ≤ n) (h13 : n ≤ 13) : type_of% (Erdos982.erdos_982 n hn) :=
  E982C.erdos_982_le_thirteen n hn h13
