/-
Erdős Problem #982 for n = 13, in the form of formal-conjectures' `Erdos982.erdos_982`: every convex 13-gon has a
vertex with at least 6 distinct distances to the other vertices. (Not obtained from n = 12, which is not settled
here: the certificate refutes `gen 13 5` directly.)
-/
import E982C.Main
import E982C.Cert13

open EuclideanGeometry

namespace E982C

theorem ccw13 (p : Fin 13 → ℝ²) (h1 : Function.Injective p) (h2 : IsCcwConvexPolygon p) :
    ∃ v : Fin 13, 6 ≤ (dset p v).ncard := ccw_of_unsat (K := 5) (by norm_num) gen_13_unsat p h1 h2

theorem erdos_982_thirteen (p : Fin 13 → ℝ²) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 13), { d : ℝ | ∃ j : Fin 13, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 13 / 2 :=
  of_ccw ccw13 p hp hp'

/-- Every n ≤ 13 except n = 12, in the form of formal-conjectures' `Erdos982.erdos_982`. -/
theorem erdos_982_le_thirteen_ne_twelve (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 13) (h12 : n ≠ 12) (p : Fin n → ℝ²)
    (hp : Function.Injective p) (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  rcases Nat.lt_or_ge n 12 with h | h
  · exact erdos_982_le_eleven n hn (by omega) p hp hp'
  · obtain rfl : n = 13 := by omega
    exact erdos_982_thirteen p hp hp'

end E982C
