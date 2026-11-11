/-
Erdős Problem #982 for n = 12, and for every 3 ≤ n ≤ 13, in the form of formal-conjectures' `Erdos982.erdos_982`:
every convex n-gon has a vertex with at least `n / 2` distinct distances to the other vertices.

n = 12: `gen 12 5` alone is satisfiable, so the CNF is `gen12` = `gen 12 5` plus 24 cut clauses. A counterclockwise
convex 12-gon with at most 5 distances at every vertex satisfies all of it under `asg p` (`genA12_eval`: the bridge
of `Bridge.lean` for `gen 12 5`; `cuts_ok` for the cuts, from the angle certificate `core_false`), while `gen12` is
refuted by a chunked LRAT certificate (`gen12_unsat`).
-/
import E982C.Cuts12
import E982C.Cert12
import E982C.Main13

open EuclideanGeometry Std.Sat

namespace E982C

theorem genA12_unsat (a : Atom 12 → Bool) : genA12.eval a = false := by
  have h2 := gen12_unsat (fun x => a (dec x))
  unfold gen12 at h2
  rw [CNF.eval_relabel] at h2
  have hc : ((fun x => a (dec x)) ∘ enc) = a := by
    funext x
    simp [dec_enc]
  rw [hc] at h2
  exact h2

/-- Every counterclockwise convex 12-gon has a vertex with at least 6 distinct distances to the other vertices. -/
theorem ccw12 (p : Fin 12 → ℝ²) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∃ v : Fin 12, 5 + 1 ≤ (dset p v).ncard := by
  by_contra h
  push Not at h
  have h1 := genA12_eval hinj hp h
  have h2 := genA12_unsat (asg p)
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **Erdős Problem #982 for n = 12**, exactly in formal-conjectures' form. -/
theorem erdos_982_twelve (p : Fin 12 → ℝ²) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 12), { d : ℝ | ∃ j : Fin 12, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 12 / 2 :=
  of_ccw ccw12 p hp hp'

/-- **Erdős Problem #982 for every 3 ≤ n ≤ 13**, in the form of formal-conjectures' `Erdos982.erdos_982`. -/
theorem erdos_982_le_thirteen (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 13) (p : Fin n → ℝ²)
    (hp : Function.Injective p) (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  rcases Nat.lt_or_ge n 12 with h | h
  · exact erdos_982_le_eleven n hn (by omega) p hp hp'
  · rcases Nat.lt_or_ge n 13 with h' | h'
    · obtain rfl : n = 12 := by omega
      exact erdos_982_twelve p hp hp'
    · obtain rfl : n = 13 := by omega
      exact erdos_982_thirteen p hp hp'

end E982C
