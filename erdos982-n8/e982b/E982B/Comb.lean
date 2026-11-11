/-
Erdős #982, n = 8, Lean part B: cyclic-order facts on the 8-cycle (by `decide`) and the orientation of polygon
triples from formal-conjectures' `IsCcwConvexPolygon`.
-/
import E982B.Geom
import E982B.Cnf

open EuclideanGeometry

namespace E982B

/-- `(i, j, k)` is in cyclic (counterclockwise index) order. -/
def csign (i j k : Fin 8) : Bool :=
  (i.val < j.val && j.val < k.val) || (j.val < k.val && k.val < i.val) || (k.val < i.val && i.val < j.val)

theorem o3_of_ccw {p : Fin 8 → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin 8} (hij : i < j) (hjk : j < k) :
    0 < o3 (p i) (p j) (p k) := by
  have h := hp hij hjk
  rw [sign_oangle_eq] at h
  exact sign_eq_one_iff.mp h

theorem orient {p : Fin 8 → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin 8}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (csign i j k = true → 0 < o3 (p i) (p j) (p k)) ∧ (csign i j k = false → o3 (p i) (p j) (p k) < 0) := by
  have r1 := o3_rotate (p i) (p j) (p k)
  have r2 := o3_rotate (p j) (p k) (p i)
  have s1 := o3_swap (p i) (p j) (p k)
  have s2 := o3_swap (p j) (p k) (p i)
  have s3 := o3_swap (p k) (p i) (p j)
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hij' with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hjk' with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hik' with h3 | h3
  · refine ⟨fun _ => o3_of_ccw hp h1 h2, fun hc => ?_⟩
    simp [csign] at hc; omega
  · omega
  · have := o3_of_ccw hp (i := i) (j := k) (k := j) h3 h2
    refine ⟨fun hc => ?_, fun _ => by linarith⟩
    simp [csign] at hc; omega
  · have := o3_of_ccw hp (i := k) (j := i) (k := j) h3 h1
    refine ⟨fun _ => by linarith, fun hc => ?_⟩
    simp [csign] at hc; omega
  · have := o3_of_ccw hp (i := j) (j := i) (k := k) h1 h3
    refine ⟨fun hc => ?_, fun _ => by linarith⟩
    simp [csign] at hc; omega
  · have := o3_of_ccw hp (i := j) (j := k) (k := i) h2 h3
    refine ⟨fun _ => by linarith, fun hc => ?_⟩
    simp [csign] at hc; omega
  · omega
  · have := o3_of_ccw hp (i := k) (j := j) (k := i) h2 h1
    refine ⟨fun hc => ?_, fun _ => by linarith⟩
    simp [csign] at hc; omega

/-! Cyclic-order facts, checked by `decide`. -/

theorem comb_l1 : ∀ u w v1 v2 : Fin 8, u ≠ w → v1 ≠ v2 → v1 ≠ u → v1 ≠ w → v2 ≠ u → v2 ≠ w →
    (isEdge u w || arcIn v1 u w == arcIn v2 u w) = true → csign v1 v2 u = csign v1 v2 w := by
  decide

theorem comb_l3d : ∀ u w a b x : Fin 8, u ≠ w → a ≠ b → a ≠ u → a ≠ w → b ≠ u → b ≠ w →
    x ≠ u → x ≠ w → x ≠ a → x ≠ b → arcIn a u w ≠ arcIn b u w →
    ((arcIn x a b == arcIn u a b) = true → csign a b x = csign a b u) ∧
    ((arcIn x a b == arcIn u a b) = false → csign a b x = csign a b w) := by
  decide

theorem comb_edge_ends : ∀ u w : Fin 8, u ≠ w → isEdge u w = true →
    (edgeStart u w = u ∧ edgeStart u w + 1 = w) ∨ (edgeStart u w = w ∧ edgeStart u w + 1 = u) := by
  decide

theorem comb_l3e : ∀ i a x : Fin 8, a ≠ i → a ≠ i + 1 → x ≠ i → x ≠ i + 1 → x ≠ a →
    (arcIn x (i + 1) a = true → csign a i x = csign a i (i + 1) ∧ csign a (i + 1) x = csign a i (i + 1)) ∧
    (arcIn x (i + 1) a = false → csign a i x ≠ csign a i (i + 1) ∧ csign a (i + 1) x ≠ csign a i (i + 1)) := by
  decide

end E982B
