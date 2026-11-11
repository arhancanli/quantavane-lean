/-
Erdős Problem #982 for every n ≤ 11, in the form of formal-conjectures' `Erdos982.erdos_982`: every convex n-gon
(`IsConvexPolygon`, strictly convex, either orientation) has a vertex with at least `n / 2` distinct distances to the
other vertices.

Even n = 4, 6, 8, 10: the bridge (`genA_eval`) and an LRAT certificate (`Cert.lean`). Odd n = 5, 7, 9, 11: delete the
last vertex. n = 3: trivial. The reflected orientation: `i ↦ p (-i)` as in formal-conjectures' definition.
-/
import E982C.Cert

open EuclideanGeometry Std.Sat

namespace E982C

/-- the set of distances from vertex `v` to the other vertices -/
def dset {n : Nat} (p : Fin n → ℝ²) (v : Fin n) : Set ℝ := {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}

theorem genA_unsat {n K : Nat} [NeZero n] (h : (gen n K).Unsat) (a : Atom n → Bool) :
    (genA n K).eval a = false := by
  have h2 := h (fun x => a (dec x))
  unfold gen at h2
  rw [CNF.eval_relabel] at h2
  have hc : ((fun x => a (dec x)) ∘ enc) = a := by
    funext x
    simp [dec_enc]
  rw [hc] at h2
  exact h2

/-- A refuted CNF `gen n K` gives: every counterclockwise convex `n`-gon has a vertex with at least `K + 1` distinct
distances to the other vertices. -/
theorem ccw_of_unsat {n K : Nat} [NeZero n] (hn : 3 ≤ n) (hU : (gen n K).Unsat) (p : Fin n → ℝ²)
    (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) : ∃ v : Fin n, K + 1 ≤ (dset p v).ncard := by
  by_contra h
  push Not at h
  have h1 := genA_eval (K := K) hn hinj hp h
  have h2 := genA_unsat hU (asg p)
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Odd from even: delete the last vertex. -/
theorem ccw_succ {m k : Nat}
    (H : ∀ p : Fin m → ℝ², Function.Injective p → IsCcwConvexPolygon p → ∃ v : Fin m, k ≤ (dset p v).ncard)
    (p : Fin (m + 1) → ℝ²) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∃ v : Fin (m + 1), k ≤ (dset p v).ncard := by
  set q : Fin m → ℝ² := fun i => p (Fin.castSucc i) with hq
  have hqinj : Function.Injective q := fun a b h => Fin.castSucc_injective _ (hinj h)
  have hqc : IsCcwConvexPolygon q := by
    intro i j k hij hjk
    exact hp (Fin.castSucc_lt_castSucc_iff.mpr hij) (Fin.castSucc_lt_castSucc_iff.mpr hjk)
  obtain ⟨v, hv⟩ := H q hqinj hqc
  refine ⟨Fin.castSucc v, le_trans hv (Set.ncard_le_ncard ?_ ?_)⟩
  · rintro d ⟨j, hj, rfl⟩
    exact ⟨Fin.castSucc j, fun h => hj (Fin.castSucc_injective _ h), rfl⟩
  · apply (Set.finite_range (fun j : Fin (m + 1) => dist (p (Fin.castSucc v)) (p j))).subset
    rintro d ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩

/-- Both orientations: formal-conjectures' `IsConvexPolygon p` means `p` or `i ↦ p (-i)` is counterclockwise. -/
theorem of_ccw {n k : Nat} [NeZero n]
    (H : ∀ p : Fin n → ℝ², Function.Injective p → IsCcwConvexPolygon p → ∃ v : Fin n, k ≤ (dset p v).ncard)
    (p : Fin n → ℝ²) (hinj : Function.Injective p) (hp : IsConvexPolygon p) :
    ∃ v : Fin n, k ≤ (dset p v).ncard := by
  rcases hp with hccw | hcw
  · exact H p hinj hccw
  · set q : Fin n → ℝ² := fun i => p (-i) with hq
    have hqinj : Function.Injective q := fun a b hab => neg_injective (hinj hab)
    obtain ⟨v, hv⟩ := H q hqinj hcw
    refine ⟨-v, ?_⟩
    have hset : dset q v = dset p (-v) := by
      ext d
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨-j, fun h => hj (neg_injective h), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨-j, fun h => hj (by rw [← h, neg_neg]), ?_⟩
        simp only [hq, neg_neg]
    rw [← hset]
    exact hv

theorem ccw4 (p : Fin 4 → ℝ²) (h1 : Function.Injective p) (h2 : IsCcwConvexPolygon p) :
    ∃ v : Fin 4, 2 ≤ (dset p v).ncard := ccw_of_unsat (K := 1) (by norm_num) gen_4_unsat p h1 h2
theorem ccw6 (p : Fin 6 → ℝ²) (h1 : Function.Injective p) (h2 : IsCcwConvexPolygon p) :
    ∃ v : Fin 6, 3 ≤ (dset p v).ncard := ccw_of_unsat (K := 2) (by norm_num) gen_6_unsat p h1 h2
theorem ccw8 (p : Fin 8 → ℝ²) (h1 : Function.Injective p) (h2 : IsCcwConvexPolygon p) :
    ∃ v : Fin 8, 4 ≤ (dset p v).ncard := ccw_of_unsat (K := 3) (by norm_num) gen_8_unsat p h1 h2
theorem ccw10 (p : Fin 10 → ℝ²) (h1 : Function.Injective p) (h2 : IsCcwConvexPolygon p) :
    ∃ v : Fin 10, 5 ≤ (dset p v).ncard := ccw_of_unsat (K := 4) (by norm_num) gen_10_unsat p h1 h2

/-- n = 3 (and any n ≥ 2): some vertex has at least one distance. -/
theorem one_le {n : Nat} [NeZero n] (hn : 2 ≤ n) (p : Fin n → ℝ²) : ∃ v : Fin n, 1 ≤ (dset p v).ncard := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  have hfin : (dset p ⟨0, by omega⟩).Finite := by
    apply (Set.finite_range (fun j : Fin n => dist (p ⟨0, by omega⟩) (p j))).subset
    rintro d ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hne : (dset p ⟨0, by omega⟩).Nonempty :=
    ⟨_, ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h, rfl⟩⟩
  exact (Set.ncard_pos hfin).mpr hne

/-- **Erdős Problem #982 for n ≤ 11**, in the form of formal-conjectures' `Erdos982.erdos_982` restricted to
`n ≤ 11`. -/
theorem erdos_982_le_eleven (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 11) (p : Fin n → ℝ²) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  interval_cases n
  · exact of_ccw (fun q _ _ => one_le (by norm_num) q) p hp hp'
  · exact of_ccw ccw4 p hp hp'
  · exact of_ccw (ccw_succ ccw4) p hp hp'
  · exact of_ccw ccw6 p hp hp'
  · exact of_ccw (ccw_succ ccw6) p hp hp'
  · exact of_ccw ccw8 p hp hp'
  · exact of_ccw (ccw_succ ccw8) p hp hp'
  · exact of_ccw ccw10 p hp hp'
  · exact of_ccw (ccw_succ ccw10) p hp hp'

/-- The case n = 10 on its own, exactly in formal-conjectures' form. -/
theorem erdos_982_ten (p : Fin 10 → ℝ²) (hp : Function.Injective p) (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 10), { d : ℝ | ∃ j : Fin 10, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 10 / 2 :=
  of_ccw ccw10 p hp hp'

/-- The case n = 11 on its own, exactly in formal-conjectures' form. -/
theorem erdos_982_eleven (p : Fin 11 → ℝ²) (hp : Function.Injective p) (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 11), { d : ℝ | ∃ j : Fin 11, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 11 / 2 :=
  of_ccw (ccw_succ ccw10) p hp hp'

end E982C
