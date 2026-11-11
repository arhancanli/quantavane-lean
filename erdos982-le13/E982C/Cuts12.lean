/-
Erdős #982, n = 12: the 24 cut clauses of `gen12` are the dihedral images of the base cut (`cuts_dec`, checked by
`decide`), so each holds for every counterclockwise convex 12-gon (`cuts_ok`, from `core_false`); with the bridge for
`gen 12 5` this gives `genA12_eval`.
-/
import E982C.Angle12

open EuclideanGeometry Std.Sat

namespace E982C

/-- the dihedral relabelling `i ↦ s - i` (`r = true`) or `i ↦ s + i` -/
def dih (r : Bool) (s : Fin 12) (i : Fin 12) : Fin 12 := if r then s - i else s + i

theorem dih_inj (r : Bool) (s : Fin 12) : Function.Injective (dih r s) := by
  intro a b h
  cases r
  · simpa [dih] using h
  · simpa [dih] using h

/-- every relation of the base cut, relabelled by `g`, is in `R` (up to the order of the two equal sides) -/
def coversB (g : Fin 12 → Fin 12) (R : List (Fin 12 × Fin 12 × Fin 12)) : Bool :=
  coreE.all fun e => decide ((g e.1, g e.2.1, g e.2.2) ∈ R) || decide ((g e.1, g e.2.2, g e.2.1) ∈ R)

theorem covers_spec {p : Fin 12 → ℝ²} {g : Fin 12 → Fin 12} {R : List (Fin 12 × Fin 12 × Fin 12)}
    (hc : coversB g R = true) (hR : ∀ r ∈ R, dist (p r.1) (p r.2.1) = dist (p r.1) (p r.2.2)) :
    ∀ e ∈ coreE, dist (p (g e.1)) (p (g e.2.1)) = dist (p (g e.1)) (p (g e.2.2)) := by
  intro e he
  unfold coversB at hc
  have h := List.all_eq_true.mp hc e he
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have h2 := hR _ h
    dsimp only at h2
    exact h2
  · have h2 := hR _ h
    dsimp only at h2
    exact h2.symm

def wits : List (Bool × Fin 12) := (List.finRange 12).flatMap fun s => [(false, s), (true, s)]

/-- each of the 24 cut relation lists is a dihedral image of the base cut, by a relabelling keeping the
betweenness facts -/
theorem cuts_dec :
    cuts12.all (fun R => wits.any fun w => coversB (dih w.1 w.2) R && betwAll (dih w.1 w.2)) = true := by
  decide +kernel

theorem cutClause_eval {p : Fin 12 → ℝ²} (R : List (Fin 12 × Fin 12 × Fin 12))
    (h : (∀ r ∈ R, dist (p r.1) (p r.2.1) = dist (p r.1) (p r.2.2)) → False) :
    (cutClause R).eval (asg p) = true := by
  by_contra hc
  apply h
  intro r hr
  simp only [Bool.not_eq_true, cutClause, CNF.Clause.eval, List.any_map, List.any_eq_false] at hc
  have h1 := hc r hr
  simpa [asg_Eq', len_cp] using h1

theorem cuts_ok {p : Fin 12 → ℝ²} (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ cuts12.map cutClause, c.eval (asg p) = true := by
  intro c hc
  obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hc
  obtain ⟨w, -, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp cuts_dec R hR)
  simp only [Bool.and_eq_true] at hw
  exact cutClause_eval R fun hall => core_false hinj hp (dih w.1 w.2) (dih_inj _ _) hw.2 (covers_spec hw.1 hall)

/-- The bridge for `gen12`: a counterclockwise convex 12-gon with at most 5 distinct distances at every vertex
satisfies every clause of `genA12` under `asg p`. -/
theorem genA12_eval {p : Fin 12 → ℝ²} (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p)
    (hK : ∀ v : Fin 12, {d : ℝ | ∃ j : Fin 12, j ≠ v ∧ d = dist (p v) (p j)}.ncard < 5 + 1) :
    genA12.eval (asg p) = true := by
  simp only [genA12, CNF.eval, List.all_toArray, List.all_append, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨eqv_ok, ord_ok⟩, class_ok hK⟩, side_ok hinj hp⟩, acute_ok (by norm_num) hinj hp⟩, cuts_ok hinj hp⟩

end E982C
