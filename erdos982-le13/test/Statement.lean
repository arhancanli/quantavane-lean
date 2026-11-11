import E982C.Main
import FormalConjectures.ErdosProblems.«982»
open EuclideanGeometry
/-- The type of formal-conjectures' `Erdos982.erdos_982 n hn`, for n ≤ 11, is inhabited by our theorem. -/
example (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 11) : type_of% (Erdos982.erdos_982 n hn) :=
  E982C.erdos_982_le_eleven n hn hn'
example : type_of% (Erdos982.erdos_982 10 (by norm_num)) := E982C.erdos_982_ten
example : type_of% (Erdos982.erdos_982 11 (by norm_num)) := E982C.erdos_982_eleven
