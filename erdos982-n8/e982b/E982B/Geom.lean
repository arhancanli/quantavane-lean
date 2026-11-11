/-
Erdős #982, n = 8, Lean part B (geometry): oriented-angle signs as coordinate determinants, and the algebraic cores
of Lemma 1 (apexes) and Lemma 3 (sides). Stated for `ℝ²` and formal-conjectures' `IsCcwConvexPolygon`.
-/
import FormalConjecturesForMathlib.Geometry.«2d»

open EuclideanGeometry

namespace E982B

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

/-! Algebraic cores. -/

/-- Lemma 1 core: if `a` and `b` are both equidistant from `u ≠ w`, then `u` and `w` lie on opposite sides of line
`ab` (or on it): the two orientation determinants sum to zero. -/
theorem o3_add_eq_zero {a b u w : ℝ²} (huw : u ≠ w) (ha : d2 a u = d2 a w) (hb : d2 b u = d2 b w) :
    o3 a b u + o3 a b w = 0 := by
  have hd := d2_pos huw
  have key : (o3 a b u + o3 a b w) * d2 u w = 0 := by
    unfold o3 d2 at *
    linear_combination
      (-((w 0 - u 0) * (b 1 - (u 1 + w 1) / 2) - (w 1 - u 1) * (b 0 - (u 0 + w 0) / 2))) * ha +
      (-((a 0 - (u 0 + w 0) / 2) * (w 1 - u 1) - (a 1 - (u 1 + w 1) / 2) * (w 0 - u 0))) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hd.ne'

/-- Lemma 3 core, diagonal case: with `a`, `b` equidistant from `u`, `w`, the difference `d2 x u - d2 x w` is a
fixed multiple of `o3 a b x`. -/
theorem side_identity (a b u w x : ℝ²) (ha : d2 a u = d2 a w) (hb : d2 b u = d2 b w) :
    (d2 x u - d2 x w) * d2 b a =
      -2 * o3 a b x * ((b 0 - a 0) * (w 1 - u 1) - (b 1 - a 1) * (w 0 - u 0)) := by
  unfold o3 d2 at *
  linear_combination
    ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 - ((b 0 - a 0) * (x 0 - a 0) + (b 1 - a 1) * (x 1 - a 1))) * ha +
    ((b 0 - a 0) * (x 0 - a 0) + (b 1 - a 1) * (x 1 - a 1)) * hb

theorem side_diag {a b u w x : ℝ²} (hab : a ≠ b) (huw : u ≠ w) (ha : d2 a u = d2 a w) (hb : d2 b u = d2 b w)
    (hs : (0 < o3 a b x ∧ 0 < o3 a b u) ∨ (o3 a b x < 0 ∧ o3 a b u < 0)) : d2 x u < d2 x w := by
  have hu := side_identity a b u w u ha hb
  have hx := side_identity a b u w x ha hb
  have he := d2_pos (Ne.symm hab)
  have hd := d2_pos huw
  have huu : d2 u u = 0 := by unfold d2; ring
  rw [huu] at hu
  set C := (b 0 - a 0) * (w 1 - u 1) - (b 1 - a 1) * (w 0 - u 0)
  -- from hu: o3 a b u * C = d2 u w * d2 b a / 2 > 0
  have hC : 0 < o3 a b u * C := by nlinarith
  have hxC : 0 < o3 a b x * C := by
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : 0 < C := by nlinarith
      exact mul_pos h1 this
    · have : C < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg h1 this
  have : (d2 x u - d2 x w) * d2 b a < 0 := by rw [hx]; nlinarith
  nlinarith

/-- Lemma 3 core, edge case: with `a` equidistant from `u`, `w`, the difference `d2 x u - d2 x w` is a fixed
multiple of `o3 a u x + o3 a w x`. -/
theorem side_identity_edge (a u w x : ℝ²) (ha : d2 a u = d2 a w) :
    (d2 x u - d2 x w) * ((u 0 + w 0 - 2 * a 0) ^ 2 + (u 1 + w 1 - 2 * a 1) ^ 2) =
      -2 * (o3 a u x + o3 a w x) *
        ((u 0 + w 0 - 2 * a 0) * (w 1 - u 1) - (u 1 + w 1 - 2 * a 1) * (w 0 - u 0)) := by
  unfold o3 d2 at *
  linear_combination
    ((u 0 + w 0 - 2 * a 0) ^ 2 + (u 1 + w 1 - 2 * a 1) ^ 2 -
      2 * ((u 0 + w 0 - 2 * a 0) * (x 0 - a 0) + (u 1 + w 1 - 2 * a 1) * (x 1 - a 1))) * ha

theorem side_edge {a u w x : ℝ²} (huw : u ≠ w) (ha : d2 a u = d2 a w) (hauw : o3 a u w ≠ 0)
    (hs : (0 < o3 a u x ∧ 0 < o3 a w x ∧ 0 < o3 a u w) ∨ (o3 a u x < 0 ∧ o3 a w x < 0 ∧ o3 a u w < 0)) :
    d2 x w < d2 x u := by
  have hw := side_identity_edge a u w w ha
  have hx := side_identity_edge a u w x ha
  have hd := d2_pos huw
  have hww : d2 w w = 0 := by unfold d2; ring
  have howw : o3 a w w = 0 := by unfold o3; ring
  have hd2 : d2 w u = d2 u w := by unfold d2; ring
  rw [hww, howw, hd2, sub_zero, add_zero] at hw
  set E := (u 0 + w 0 - 2 * a 0) ^ 2 + (u 1 + w 1 - 2 * a 1) ^ 2 with hEdef
  set C := (u 0 + w 0 - 2 * a 0) * (w 1 - u 1) - (u 1 + w 1 - 2 * a 1) * (w 0 - u 0)
  have hE : 0 < E := by
    rcases (show 0 ≤ E by positivity).lt_or_eq with h | h
    · exact h
    · exfalso; apply hauw
      have hh := (add_eq_zero_iff_of_nonneg (sq_nonneg (u 0 + w 0 - 2 * a 0)) (sq_nonneg (u 1 + w 1 - 2 * a 1))).mp
        (by rw [← hEdef]; exact h.symm)
      have e0 : a 0 = (u 0 + w 0) / 2 := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hh.1; linarith
      have e1 : a 1 = (u 1 + w 1) / 2 := by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hh.2; linarith
      unfold o3
      rw [e0, e1]; ring
  -- hw : d2 u w * E = -2 * o3 a u w * C
  have hprod : o3 a u w * C < 0 := by
    have : 0 < d2 u w * E := mul_pos hd hE
    linarith
  have hgC : (o3 a u x + o3 a w x) * C < 0 := by
    rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hC : C < 0 := by
        by_contra hc; push_neg at hc
        have : 0 ≤ o3 a u w * C := mul_nonneg h3.le hc
        linarith
      exact mul_neg_of_pos_of_neg (by linarith) hC
    · have hC : 0 < C := by
        by_contra hc; push_neg at hc
        have : 0 ≤ o3 a u w * C := mul_nonneg_of_nonpos_of_nonpos h3.le hc
        linarith
      exact mul_neg_of_neg_of_pos (by linarith) hC
  have hpos : 0 < (d2 x u - d2 x w) * E := by rw [hx]; linarith
  have : 0 < d2 x u - d2 x w := pos_of_mul_pos_left hpos hE.le
  linarith

end E982B
