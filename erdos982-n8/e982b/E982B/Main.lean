/-
Erdős Problem #982, the case n = 8, in the form of formal-conjectures' `Erdos982.erdos_982` with `n = 8`:
every convex octagon (`IsConvexPolygon`, strictly convex, either orientation) has a vertex with at least
`8 / 2 = 4` distinct distances to the other vertices.
-/
import E982B.Bridge

open EuclideanGeometry

namespace E982B

theorem not_all_small (p : Fin 8 → ℝ²) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ¬ ∀ v : Fin 8, {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (p v) (p j)}.ncard < 4 := by
  intro hK
  have h1 := genA_eval hinj hp hK
  have h2 := genA_unsat (asg p)
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem erdos_982_eight (p : Fin 8 → ℝ²) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 8), { d : ℝ | ∃ j : Fin 8, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 8 / 2 := by
  by_contra h
  push_neg at h
  have h4 : ∀ v : Fin 8, {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (p v) (p j)}.ncard < 4 := by
    intro v
    have := h v
    norm_num at this
    exact this
  rcases hp' with hccw | hcw
  · exact not_all_small p hp hccw h4
  · set q : Fin 8 → ℝ² := fun i => p (-i) with hq
    have hqinj : Function.Injective q := fun a b hab => neg_injective (hp hab)
    apply not_all_small q hqinj hcw
    intro v
    have hset : {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (q v) (q j)} =
        {d : ℝ | ∃ j : Fin 8, j ≠ -v ∧ d = dist (p (-v)) (p j)} := by
      ext d
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨-j, fun h => hj (neg_injective h), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨-j, fun h => hj (by rw [← h, neg_neg]), ?_⟩
        simp only [hq, neg_neg]
    rw [hset]
    exact h4 (-v)

end E982B
