/-
Erdős #982, n = 12 (geometry): unoriented angles at the vertices of a counterclockwise convex polygon.
  * `T_th`: the angles of a triangle of vertices sum to `π`;
  * `E_th`: equal sides from `o` give equal base angles;
  * `A_th`: if `y` lies strictly between `x` and `z` in the cyclic order seen from `v`, the angle at `v` splits:
    `∠ x v z = ∠ x v y + ∠ y v z` (from Mathlib's oriented angles: all three oriented angles have sign `1` there,
    so they equal the unoriented ones, and the sum taken modulo `2π` is exact because each angle lies in `(0, π)`).
-/
import E982C.Bridge

open EuclideanGeometry

namespace E982C

/-- `y` lies strictly between `x` and `z` in the cyclic order of the polygon seen from `v` -/
def betwB {n : Nat} (v x y z : Fin n) : Bool := (cycB v x y && cycB v y z) || (cycB v z y && cycB v y x)

/-- the unoriented angle at vertex `v` between vertices `a` and `b` -/
noncomputable def th {n : Nat} (p : Fin n → ℝ²) (v a b : Fin n) : ℝ := ∠ (p a) (p v) (p b)

variable {n : Nat} {p : Fin n → ℝ²}

theorem th_comm (v a b : Fin n) : th p v a b = th p v b a := angle_comm _ _ _

theorem th_nonneg (v a b : Fin n) : 0 ≤ th p v a b := angle_nonneg _ _ _

theorem th_le_pi (v a b : Fin n) : th p v a b ≤ Real.pi := angle_le_pi _ _ _

/-- The angle sum of a triangle of vertices. -/
theorem T_th (hinj : Function.Injective p) {a b : Fin n} (c : Fin n) (hab : a ≠ b) :
    th p a b c + th p b a c + th p c a b = Real.pi := by
  have h := angle_add_angle_add_angle_eq_pi (p₁ := p b) (p₂ := p a) (p c) (fun h => hab (hinj h))
  unfold th
  rw [angle_comm (p a) (p b) (p c)]
  linarith

/-- Base angles of an isosceles triangle. -/
theorem E_th {o a b : Fin n} (h : dist (p o) (p a) = dist (p o) (p b)) : th p a o b = th p b o a :=
  angle_eq_angle_of_dist_eq h

/-- Additivity of unoriented angles when the three oriented angles are positive. -/
theorem angle_add_of_sign {x v y z : ℝ²} (h1 : (∡ x v y).sign = 1) (h2 : (∡ y v z).sign = 1)
    (h3 : (∡ x v z).sign = 1) : ∠ x v z = ∠ x v y + ∠ y v z := by
  have hx : x ≠ v := left_ne_of_oangle_sign_ne_zero (by rw [h1]; decide)
  have hy : y ≠ v := left_ne_of_oangle_sign_ne_zero (by rw [h2]; decide)
  have hz : z ≠ v := right_ne_of_oangle_sign_ne_zero (by rw [h3]; decide)
  have hadd := oangle_add hx hy hz
  have e1 := oangle_eq_angle_of_sign_eq_one h1
  have e2 := oangle_eq_angle_of_sign_eq_one h2
  have e3 := oangle_eq_angle_of_sign_eq_one h3
  rw [e1, e2, e3, ← Real.Angle.coe_add] at hadd
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hadd
  have s1 : ∠ x v y ≠ Real.pi := by
    intro h; rw [e1, h, Real.Angle.sign_coe_pi] at h1; exact absurd h1 (by decide)
  have s3 : ∠ x v z ≠ 0 := by
    intro h; rw [e3, h, Real.Angle.coe_zero, Real.Angle.sign_zero] at h3; exact absurd h3 (by decide)
  have b1 := angle_nonneg x v y
  have b2 := angle_le_pi x v y
  have b3 := angle_nonneg y v z
  have b4 := angle_le_pi y v z
  have b5 := angle_nonneg x v z
  have b6 := angle_le_pi x v z
  have l1 : ∠ x v y < Real.pi := lt_of_le_of_ne b2 s1
  have l3 : 0 < ∠ x v z := lt_of_le_of_ne b5 (Ne.symm s3)
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc
    push Not at hc
    have : 2 * Real.pi * 1 ≤ 2 * Real.pi * k := mul_le_mul_of_nonneg_left hc (by linarith)
    linarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc
    push Not at hc
    have : 2 * Real.pi * k ≤ 2 * Real.pi * (-1) := mul_le_mul_of_nonneg_left hc (by linarith)
    linarith
  have hk0 : k = 0 := by
    have i1 : k < 1 := by exact_mod_cast hk1
    have i2 : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0, Int.cast_zero, mul_zero] at hk
  linarith

theorem sign_of_cyc (hp : IsCcwConvexPolygon p) {i j k : Fin n} (h : cycP i j k) :
    (∡ (p i) (p j) (p k)).sign = 1 := by
  obtain ⟨hij, hjk, hik⟩ := cycP_ne h
  rw [sign_oangle_eq]
  exact sign_pos ((orient hp hij hjk hik).1 h)

/-- The angle at a vertex splits at any vertex strictly between the two sides. -/
theorem A_th (hp : IsCcwConvexPolygon p) {v x y z : Fin n} (h : betwB v x y z = true) :
    th p v x z = th p v x y + th p v y z := by
  unfold betwB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, cyc_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have c1 : cycP z v y := by unfold cycP at *; omega
    have c2 : cycP y v x := by unfold cycP at *; omega
    have c3 : cycP z v x := by unfold cycP at *; omega
    have := angle_add_of_sign (sign_of_cyc hp c1) (sign_of_cyc hp c2) (sign_of_cyc hp c3)
    unfold th
    rw [angle_comm (p x) (p v) (p z), angle_comm (p x) (p v) (p y), angle_comm (p y) (p v) (p z)]
    linarith
  · have c1 : cycP x v y := by unfold cycP at *; omega
    have c2 : cycP y v z := by unfold cycP at *; omega
    have c3 : cycP x v z := by unfold cycP at *; omega
    exact angle_add_of_sign (sign_of_cyc hp c1) (sign_of_cyc hp c2) (sign_of_cyc hp c3)

end E982C
