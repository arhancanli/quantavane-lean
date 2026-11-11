/-
Erdős #982, round 2 (geometry): oriented-angle signs as coordinate determinants (from E982B.Geom), and the
algebraic cores of the two lemmas used by the finite check:
  * `side_core`: four vertices in cyclic order and an affine function (here `d2 · u - d2 · w`): the half-plane rule.
  * `acute_of_le_left/right`, `cone_pos`, `quad_not_all_acute`: no four acute angles in a convex polygon.
Stated for `ℝ²`.
-/
import FormalConjecturesForMathlib.Geometry.«2d»

open EuclideanGeometry

namespace E982C

/-- The orientation determinant matching `∡ a b c` (see `sign_oangle_eq`). -/
noncomputable def o3 (a b c : ℝ²) : ℝ := (a 0 - b 0) * (c 1 - b 1) - (a 1 - b 1) * (c 0 - b 0)

theorem o3_rotate (a b c : ℝ²) : o3 b c a = o3 a b c := by unfold o3; ring
theorem o3_swap (a b c : ℝ²) : o3 a c b = - o3 a b c := by unfold o3; ring

theorem areaForm_eq_mul_sin (x y : ℝ²) :
    (positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).areaForm x y =
      ‖x‖ * ‖y‖ * Real.Angle.sin ((positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).oangle x y) := by
  set o := positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Orientation.oangle, Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler]
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have him : (o.kahler x y).im = o.areaForm x y := by
    simp [Orientation.kahler_apply_apply, Complex.real_smul]
  rw [him]
  field_simp

theorem areaForm_eq_o3 (a b c : ℝ²) :
    (positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).areaForm (a -ᵥ b) (c -ᵥ b) = o3 a b c := by
  have h := triangle_area_eq_det a c b
  unfold triangle_area at h
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const] at h
  unfold o3
  linarith

theorem sign_oangle_eq (a b c : ℝ²) : (∡ a b c).sign = SignType.sign (o3 a b c) := by
  rw [← areaForm_eq_o3]
  unfold EuclideanGeometry.oangle Real.Angle.sign
  rw [areaForm_eq_mul_sin]
  set x := a -ᵥ b
  set y := c -ᵥ b
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  rw [sign_mul, sign_pos hpos, one_mul]

/-! Squared distances in coordinates. -/

noncomputable def d2 (a b : ℝ²) : ℝ := (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2

theorem d2_nonneg (a b : ℝ²) : 0 ≤ d2 a b := by unfold d2; positivity

theorem d2_comm (a b : ℝ²) : d2 a b = d2 b a := by unfold d2; ring

theorem d2_self (a : ℝ²) : d2 a a = 0 := by unfold d2; ring

theorem dist_eq_sqrt_d2 (a b : ℝ²) : dist a b = Real.sqrt (d2 a b) := by
  rw [EuclideanSpace.dist_eq]
  simp [d2, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_eq_iff_d2 (a b c d : ℝ²) : dist a b = dist c d ↔ d2 a b = d2 c d := by
  rw [dist_eq_sqrt_d2, dist_eq_sqrt_d2]
  exact Real.sqrt_inj (d2_nonneg _ _) (d2_nonneg _ _)

theorem dist_lt_iff_d2 (a b c d : ℝ²) : dist a b < dist c d ↔ d2 a b < d2 c d := by
  rw [dist_eq_sqrt_d2, dist_eq_sqrt_d2]
  exact Real.sqrt_lt_sqrt_iff (d2_nonneg _ _)

theorem d2_pos {a b : ℝ²} (h : a ≠ b) : 0 < d2 a b := by
  rcases (d2_nonneg a b).lt_or_eq with h' | h'
  · exact h'
  · exfalso; apply h
    have h0 : (a 0 - b 0) ^ 2 = 0 := by unfold d2 at h'; nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    have h1 : (a 1 - b 1) ^ 2 = 0 := by unfold d2 at h'; nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    ext i
    fin_cases i
    · simpa [sub_eq_zero] using h0
    · simpa [sub_eq_zero] using h1

/-! The half-plane rule. -/

/-- Four points `u, y, z, w` in cyclic order (all four triangle orientations of one strict sign `σ`): if `z` is not
farther from `u` than from `w`, then `y` is strictly nearer to `u` than to `w`. The function
`F p = d2 p u - d2 p w` is affine, and four points satisfy
`o3 u z w * F y = o3 y z w * F u + o3 u y w * F z - o3 u y z * F w`. -/
theorem side_core {u w y z : ℝ²} (huw : u ≠ w) (σ : ℝ)
    (h1 : 0 < σ * o3 u y z) (h2 : 0 < σ * o3 u y w) (h3 : 0 < σ * o3 u z w) (h4 : 0 < σ * o3 y z w)
    (hz : d2 z u ≤ d2 z w) : d2 y u < d2 y w := by
  have hd := d2_pos huw
  have key : o3 u z w * (d2 y u - d2 y w) =
      o3 y z w * (d2 u u - d2 u w) + o3 u y w * (d2 z u - d2 z w) - o3 u y z * (d2 w u - d2 w w) := by
    unfold o3 d2; ring
  rw [d2_self, d2_self, d2_comm w u] at key
  have k2 : (σ * o3 u z w) * (d2 y u - d2 y w) =
      (σ * o3 y z w) * (0 - d2 u w) + (σ * o3 u y w) * (d2 z u - d2 z w) - (σ * o3 u y z) * (d2 u w - 0) := by
    rw [mul_assoc, key]; ring
  have t1 : (σ * o3 y z w) * (0 - d2 u w) < 0 := mul_neg_of_pos_of_neg h4 (by linarith)
  have t2 : (σ * o3 u y w) * (d2 z u - d2 z w) ≤ 0 := by nlinarith
  have t3 : 0 < (σ * o3 u y z) * (d2 u w - 0) := mul_pos h1 (by linarith)
  have t4 : (σ * o3 u z w) * (d2 y u - d2 y w) < 0 := by rw [k2]; linarith
  by_contra hc
  push_neg at hc
  have : 0 ≤ (σ * o3 u z w) * (d2 y u - d2 y w) := mul_nonneg h3.le (by linarith)
  linarith

/-! Acute angles. -/

/-- `dt a b c`: the dot product of `a - b` and `c - b` (positive iff the angle at `b` is acute). -/
noncomputable def dt (a b c : ℝ²) : ℝ := (a 0 - b 0) * (c 0 - b 0) + (a 1 - b 1) * (c 1 - b 1)

theorem cosine (a b c : ℝ²) : d2 a c = d2 a b + d2 b c - 2 * dt a b c := by unfold d2 dt; ring

theorem acute_of_le_left {a b c : ℝ²} (hbc : b ≠ c) (h : d2 a c ≤ d2 a b) : 0 < dt a b c := by
  have := cosine a b c
  have := d2_pos hbc
  linarith

theorem acute_of_le_right {a b c : ℝ²} (hab : a ≠ b) (h : d2 a c ≤ d2 b c) : 0 < dt a b c := by
  have := cosine a b c
  have := d2_pos hab
  linarith

theorem cone_identity (a v b x : ℝ²) (k : Fin 2) :
    o3 a v b * (x k - v k) = o3 x v b * (a k - v k) + o3 a v x * (b k - v k) := by
  fin_cases k <;> simp [o3] <;> ring

theorem cone_dot_identity (a v b x y : ℝ²) :
    dt x v y * (o3 a v b) ^ 2 = o3 x v b * o3 y v b * d2 a v +
      (o3 x v b * o3 a v y + o3 a v x * o3 y v b) * dt a v b + o3 a v x * o3 a v y * d2 b v := by
  unfold dt o3 d2; ring

theorem cone_coeff_pos {a v b x : ℝ²} (hO : 0 < o3 a v b) (hx : x ≠ v)
    (h1 : 0 ≤ o3 x v b) (h2 : 0 ≤ o3 a v x) : 0 < o3 x v b + o3 a v x := by
  rcases (add_nonneg h1 h2).lt_or_eq with h | h
  · exact h
  · exfalso
    have e1 : o3 x v b = 0 := by linarith
    have e2 : o3 a v x = 0 := by linarith
    apply hx
    ext k
    have := cone_identity a v b x k
    rw [e1, e2] at this
    have h0 : o3 a v b * (x k - v k) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith

/-- The cone lemma: if the angle at `v` between `a` and `b` is acute (and `a, v, b` are positively oriented), then
so is the angle at `v` between any two points `x, y ≠ v` of the cone spanned by `a - v` and `b - v`. -/
theorem cone_pos {a v b x y : ℝ²} (hO : 0 < o3 a v b) (hab : 0 < dt a v b) (ha : a ≠ v) (hb : b ≠ v)
    (hx : x ≠ v) (hy : y ≠ v) (hx1 : 0 ≤ o3 x v b) (hx2 : 0 ≤ o3 a v x) (hy1 : 0 ≤ o3 y v b)
    (hy2 : 0 ≤ o3 a v y) : 0 < dt x v y := by
  have hA := d2_pos ha
  have hB := d2_pos hb
  have sx := cone_coeff_pos hO hx hx1 hx2
  have sy := cone_coeff_pos hO hy hy1 hy2
  have hid := cone_dot_identity a v b x y
  set α := o3 x v b
  set β := o3 a v x
  set γ := o3 y v b
  set δ := o3 a v y
  set m := min (min (d2 a v) (dt a v b)) (d2 b v) with hm
  have hm0 : 0 < m := lt_min (lt_min hA hab) hB
  have hmA : m ≤ d2 a v := (min_le_left _ _).trans (min_le_left _ _)
  have hmD : m ≤ dt a v b := (min_le_left _ _).trans (min_le_right _ _)
  have hmB : m ≤ d2 b v := min_le_right _ _
  have p1 : α * γ * m ≤ α * γ * d2 a v := mul_le_mul_of_nonneg_left hmA (mul_nonneg hx1 hy1)
  have p2 : (α * δ + β * γ) * m ≤ (α * δ + β * γ) * dt a v b :=
    mul_le_mul_of_nonneg_left hmD (add_nonneg (mul_nonneg hx1 hy2) (mul_nonneg hx2 hy1))
  have p3 : β * δ * m ≤ β * δ * d2 b v := mul_le_mul_of_nonneg_left hmB (mul_nonneg hx2 hy2)
  have hprod : 0 < (α + β) * (γ + δ) * m := mul_pos (mul_pos sx sy) hm0
  have hsq : 0 < (o3 a v b) ^ 2 := by positivity
  have hpos : 0 < dt x v y * (o3 a v b) ^ 2 := by
    rw [hid]; nlinarith
  by_contra hc
  push_neg at hc
  have : dt x v y * (o3 a v b) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hsq.le
  linarith

theorem quad_identity (A B C D : ℝ²) :
    o3 B C D * dt D A B + o3 A C D * dt A B C + o3 A B D * dt B C D + o3 A B C * dt C D A = 0 := by
  unfold o3 dt; ring

/-- A convex quadrilateral `A B C D` (positively oriented) has no four acute angles. -/
theorem quad_not_all_acute {A B C D : ℝ²} (h1 : 0 < o3 A B C) (h2 : 0 < o3 A B D) (h3 : 0 < o3 A C D)
    (h4 : 0 < o3 B C D) (hA : 0 < dt D A B) (hB : 0 < dt A B C) (hC : 0 < dt B C D) (hD : 0 < dt C D A) :
    False := by
  have := quad_identity A B C D
  have := mul_pos h4 hA
  have := mul_pos h3 hB
  have := mul_pos h2 hC
  have := mul_pos h1 hD
  linarith

end E982C
