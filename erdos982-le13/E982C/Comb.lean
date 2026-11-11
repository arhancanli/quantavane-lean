/-
Erdős #982, round 2: index combinatorics on the `n`-cycle (all by `omega`) and the orientation of polygon triples
from formal-conjectures' `IsCcwConvexPolygon`.
-/
import E982C.Geom
import E982C.Code

open EuclideanGeometry

namespace E982C

variable {n : Nat}

/-- strict cyclic order of three indices, as a proposition -/
def cycP (a b c : Fin n) : Prop :=
  (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨ (c.val < a.val ∧ a.val < b.val)

instance (a b c : Fin n) : Decidable (cycP a b c) := by unfold cycP; infer_instance

theorem cycB_eq (a b c : Fin n) : cycB a b c = decide (cycP a b c) := by
  unfold cycB cycP
  by_cases h1 : a.val < b.val <;> by_cases h2 : b.val < c.val <;> by_cases h3 : c.val < a.val <;> simp [h1, h2, h3]

theorem cyc_true {a b c : Fin n} : cycB a b c = true ↔ cycP a b c := by
  rw [cycB_eq]; exact decide_eq_true_iff

theorem btw_true {u y z w : Fin n} :
    btwB u y z w = true ↔ (cycP u y z ∧ cycP u z w) ∨ (cycP w z y ∧ cycP w y u) := by
  unfold btwB
  simp only [Bool.or_eq_true, Bool.and_eq_true, cyc_true]

/-- Four vertices `u, y, z, w` with `y` strictly inside the arc from `u` to `z` that avoids `w`: they are distinct and
in cyclic order, counterclockwise or clockwise. -/
theorem btw_cases {u y z w : Fin n} (h : btwB u y z w = true) :
    u ≠ y ∧ u ≠ z ∧ u ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
    ((cycP u y z ∧ cycP u y w ∧ cycP u z w ∧ cycP y z w) ∨
     (¬ cycP u y z ∧ ¬ cycP u y w ∧ ¬ cycP u z w ∧ ¬ cycP y z w)) := by
  rw [btw_true] at h
  simp only [ne_eq, Fin.ext_iff]
  unfold cycP at *
  omega

theorem o3_of_ccw {p : Fin n → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    0 < o3 (p i) (p j) (p k) := by
  have h := hp hij hjk
  rw [sign_oangle_eq] at h
  exact sign_eq_one_iff.mp h

theorem orient {p : Fin n → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (cycP i j k → 0 < o3 (p i) (p j) (p k)) ∧ (¬ cycP i j k → o3 (p i) (p j) (p k) < 0) := by
  have r1 := o3_rotate (p i) (p j) (p k)
  have r2 := o3_rotate (p j) (p k) (p i)
  have s1 := o3_swap (p i) (p j) (p k)
  have s2 := o3_swap (p j) (p k) (p i)
  have s3 := o3_swap (p k) (p i) (p j)
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  unfold cycP
  rcases Nat.lt_or_gt_of_ne hij' with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hjk' with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hik' with h3 | h3
  · exact ⟨fun _ => o3_of_ccw hp h1 h2, fun hc => absurd (Or.inl ⟨h1, h2⟩) hc⟩
  · omega
  · have := o3_of_ccw hp (i := i) (j := k) (k := j) h3 h2
    exact ⟨fun hc => by omega, fun _ => by linarith⟩
  · have := o3_of_ccw hp (i := k) (j := i) (k := j) h3 h1
    exact ⟨fun _ => by linarith, fun hc => absurd (Or.inr (Or.inr ⟨h3, h1⟩)) hc⟩
  · have := o3_of_ccw hp (i := j) (j := i) (k := k) h1 h3
    exact ⟨fun hc => by omega, fun _ => by linarith⟩
  · have := o3_of_ccw hp (i := j) (j := k) (k := i) h2 h3
    exact ⟨fun _ => by linarith, fun hc => absurd (Or.inr (Or.inl ⟨h2, h3⟩)) hc⟩
  · omega
  · have := o3_of_ccw hp (i := k) (j := j) (k := i) h2 h1
    exact ⟨fun hc => by omega, fun _ => by linarith⟩

/-! Neighbours of a vertex. -/

variable [NeZero n]

theorem nx_val (v : Fin n) : (nx n v).val = if v.val + 1 < n then v.val + 1 else 0 := by
  unfold nx fm
  simp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : v.val + 1 = n := by have := v.isLt; omega
    rw [this, Nat.mod_self]

theorem pv_val (v : Fin n) : (pv n v).val = if 0 < v.val then v.val - 1 else n - 1 := by
  unfold pv fm
  simp only
  split_ifs with h
  · have e : v.val + n - 1 = (v.val - 1) + n := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := v.isLt; omega)]
  · have e : v.val = 0 := by omega
    have := n_pos (n := n)
    rw [e, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

theorem nb_facts (hn : 3 ≤ n) (v : Fin n) :
    pv n v ≠ v ∧ nx n v ≠ v ∧ pv n v ≠ nx n v ∧ cycP (pv n v) v (nx n v) := by
  have h1 := nx_val v
  have h2 := pv_val v
  have := v.isLt
  simp only [ne_eq, Fin.ext_iff]
  unfold cycP
  split_ifs at h1 h2 <;> omega

theorem nb_x (v x : Fin n) (hx : x ≠ v) :
    (x = nx n v ∨ cycP x v (nx n v)) ∧ (x = pv n v ∨ cycP (pv n v) v x) := by
  have h1 := nx_val v
  have h2 := pv_val v
  have := v.isLt
  have := x.isLt
  have hx' : x.val ≠ v.val := fun h => hx (Fin.ext h)
  simp only [Fin.ext_iff]
  unfold cycP
  split_ifs at h1 h2 <;> omega

end E982C
