/-
Erdős #982, round 2: the bridge. A strictly convex `n`-gon (formal-conjectures' `IsCcwConvexPolygon`, `n ≥ 3`) with at
most `K` distinct distances at every vertex gives an assignment of the atoms satisfying every clause of `genA n K`.
-/
import E982C.Comb

open EuclideanGeometry Std.Sat

namespace E982C

/-! List facts. -/

theorem mem_pairsOf {α : Type} {L : List α} {x y : α} (h : (x, y) ∈ pairsOf L) :
    x ∈ L ∧ y ∈ L ∧ (L.Nodup → x ≠ y) := by
  induction L with
  | nil => simp [pairsOf] at h
  | cons z zs ih =>
    simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨t, ht, rfl, rfl⟩ | h
    · refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ ht, fun hn => ?_⟩
      rintro rfl
      exact (List.nodup_cons.mp hn).1 ht
    · obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, fun hn => h3 (List.nodup_cons.mp hn).2⟩

theorem pairsOf_of_mem {α : Type} {L : List α} {x y : α} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    (x, y) ∈ pairsOf L ∨ (y, x) ∈ pairsOf L := by
  induction L with
  | nil => simp at hx
  | cons z zs ih =>
    simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact Or.inl (Or.inl ⟨y, hy', rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, hx', rfl, rfl⟩)
    · rcases ih hx' hy' with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem mem_subsets {α : Type} : ∀ {k : Nat} {L S : List α}, S ∈ subsets k L → S.Sublist L ∧ S.length = k
  | 0, L, S, h => by simp [subsets] at h; subst h; exact ⟨List.nil_sublist _, rfl⟩
  | _ + 1, [], S, h => by simp [subsets] at h
  | k + 1, x :: xs, S, h => by
    simp only [subsets, List.mem_append, List.mem_map] at h
    rcases h with ⟨T, hT, rfl⟩ | h
    · obtain ⟨h1, h2⟩ := mem_subsets hT
      exact ⟨h1.cons_cons x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := mem_subsets h
      exact ⟨h1.cons x, h2⟩

variable {n : Nat}

theorem vs_nodup : (vs n).Nodup := List.nodup_finRange n

theorem cycP_ne {a b c : Fin n} (h : cycP a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  unfold cycP at h
  simp only [ne_eq, Fin.ext_iff]
  omega

/-! The assignment given by a polygon. -/

variable (p : Fin n → ℝ²)

noncomputable def len (P : Fin n × Fin n) : ℝ := dist (p P.1) (p P.2)

variable [NeZero n]

/-- the interior angle at `v` is acute -/
def acute (v : Fin n) : Prop := 0 < dt (p (pv n v)) (p v) (p (nx n v))

noncomputable instance (v : Fin n) : Decidable (acute p v) := by unfold acute; infer_instance

noncomputable def asg : Atom n → Bool
  | .E P Q => decide (len p P = len p Q)
  | .L P Q => decide (len p P < len p Q)
  | .A v => decide (acute p v)

theorem len_cp (u w : Fin n) : len p (cp u w) = dist (p u) (p w) := by
  unfold cp len; split <;> simp [dist_comm]

theorem asg_Eq' (P Q : Fin n × Fin n) : asg p (Eq' P Q) = decide (len p P = len p Q) := by
  unfold Eq'; split
  · rfl
  · simp only [asg, eq_comm]

theorem asg_L (P Q : Fin n × Fin n) : asg p (.L P Q) = decide (len p P < len p Q) := rfl

theorem asg_A (v : Fin n) : asg p (.A v) = decide (acute p v) := rfl

variable {p}

theorem d2_le_of_dist_le {a b c d : ℝ²} (h : dist a b ≤ dist c d) : d2 a b ≤ d2 c d := by
  rcases h.lt_or_eq with h | h
  · exact ((dist_lt_iff_d2 _ _ _ _).mp h).le
  · exact ((dist_eq_iff_d2 _ _ _ _).mp h).le

/-! Each clause family is satisfied. -/

theorem eqv_ok : ∀ c ∈ eqvCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [eqvCls, List.mem_flatMap] at hc
  obtain ⟨P, -, Q, -, R, -, hc⟩ := hc
  split_ifs at hc with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', Bool.or_false]
    by_cases h1 : len p P = len p Q <;> by_cases h2 : len p Q = len p R <;> simp [h1, h2] <;> linarith
  · simp at hc

theorem ord_ok : ∀ c ∈ ordCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [ordCls, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨P, -, Q, -, hc⟩ | ⟨P, -, Q, -, R, -, hc⟩
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', asg_L, Bool.or_false]
      · by_cases h1 : len p P = len p Q <;> simp [h1]
      · rcases lt_trichotomy (len p P) (len p Q) with h1 | h1 | h1 <;> simp [h1]
    · simp at hc
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_L, Bool.or_false]
      by_cases h1 : len p P < len p Q <;> by_cases h2 : len p Q < len p R <;> simp [h1, h2] <;> linarith
    · simp at hc

theorem class_ok {K : Nat}
    (hK : ∀ v : Fin n, {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}.ncard < K + 1) :
    ∀ c ∈ classCls n K, c.eval (asg p) = true := by
  intro c hc
  simp only [classCls, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨v, -, S, hS, rfl⟩ := hc
  obtain ⟨hsub, hlen⟩ := mem_subsets hS
  have hnd : S.Nodup := (vs_nodup.filter _).sublist hsub
  have hne : ∀ j ∈ S, j ≠ v := fun j hj => by
    have := hsub.subset hj
    simp only [others, List.mem_filter, bne_iff_ne] at this
    exact this.2
  set D := {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)} with hDdef
  have hDfin : D.Finite := by
    have : D ⊆ Set.range (fun j : Fin n => dist (p v) (p j)) := by
      rintro d ⟨j, -, rfl⟩; exact ⟨j, rfl⟩
    exact (Set.finite_range _).subset this
  obtain ⟨x, hx, y, hy, hxy, heq⟩ : ∃ x ∈ S.toFinset, ∃ y ∈ S.toFinset, x ≠ y ∧
      dist (p v) (p x) = dist (p v) (p y) := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := hDfin.toFinset)
    · rw [List.toFinset_card_of_nodup hnd, hlen, ← Set.ncard_eq_toFinset_card D hDfin]
      exact hK v
    · intro j hj
      simp only [Finset.mem_coe, List.mem_toFinset] at hj
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, hDdef, Set.mem_setOf_eq]
      exact ⟨j, hne j hj, rfl⟩
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  rcases pairsOf_of_mem (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy with h | h
  · exact ⟨(x, y), h, by simp [asg_Eq', len_cp, heq]⟩
  · exact ⟨(y, x), h, by simp [asg_Eq', len_cp, heq]⟩

theorem side_ok (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ sideCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [sideCls, List.mem_flatMap] at hc
  obtain ⟨u, -, w, -, z, -, y, -, hc⟩ := hc
  split_ifs at hc with hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    obtain ⟨huy, huz, huw, hyz, hyw, hzw, hcyc⟩ := btw_cases hb
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_L, len_cp]
    by_cases h1 : dist (p z) (p w) < dist (p z) (p u)
    · simp [h1]
    · have hz : d2 (p z) (p u) ≤ d2 (p z) (p w) := d2_le_of_dist_le (not_lt.mp h1)
      have hpuw : p u ≠ p w := fun h => huw (hinj h)
      have o1 := orient hp huy hyz huz
      have o2 := orient hp huy hyw huw
      have o3' := orient hp huz hzw huw
      have o4 := orient hp hyz hzw hyw
      have key : d2 (p y) (p u) < d2 (p y) (p w) := by
        rcases hcyc with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
        · refine side_core hpuw 1 ?_ ?_ ?_ ?_ hz
          · rw [one_mul]; exact o1.1 c1
          · rw [one_mul]; exact o2.1 c2
          · rw [one_mul]; exact o3'.1 c3
          · rw [one_mul]; exact o4.1 c4
        · refine side_core hpuw (-1) ?_ ?_ ?_ ?_ hz
          · have := o1.2 c1; linarith
          · have := o2.2 c2; linarith
          · have := o3'.2 c3; linarith
          · have := o4.2 c4; linarith
      have : dist (p y) (p u) < dist (p y) (p w) := (dist_lt_iff_d2 _ _ _ _).mpr key
      simp [this]
  · simp at hc

/-- The cone lemma at a vertex of the polygon. -/
theorem cone_at (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) {v x y : Fin n}
    (hx : x ≠ v) (hy : y ≠ v) (hv : acute p v) : 0 < dt (p x) (p v) (p y) := by
  obtain ⟨hpv, hnx, hpn, hcyc⟩ := nb_facts hn v
  have hO := (orient hp hpv hnx.symm hpn).1 hcyc
  have coeff : ∀ z : Fin n, z ≠ v → 0 ≤ o3 (p z) (p v) (p (nx n v)) ∧ 0 ≤ o3 (p (pv n v)) (p v) (p z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := nb_x v z hz
    constructor
    · rcases h1 with h1 | h1
      · rw [h1]; exact le_of_eq (by unfold o3; ring)
      · exact ((orient hp hz hnx.symm (cycP_ne h1).2.2).1 h1).le
    · rcases h2 with h2 | h2
      · rw [h2]; exact le_of_eq (by unfold o3; ring)
      · exact ((orient hp hpv (Ne.symm hz) (cycP_ne h2).2.2).1 h2).le
  exact cone_pos hO hv (fun h => hpv (hinj h)) (fun h => hnx (hinj h)) (fun h => hx (hinj h))
    (fun h => hy (hinj h)) (coeff x hx).1 (coeff x hx).2 (coeff y hy).1 (coeff y hy).2

theorem no_four_acute (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (ha : acute p a) (hb : acute p b) (hc : acute p c)
    (hd : acute p d) : False := by
  have hac : a < c := lt_trans hab hbc
  have hbd : b < d := lt_trans hbc hcd
  have had : a < d := lt_trans hac hcd
  exact quad_not_all_acute (o3_of_ccw hp hab hbc) (o3_of_ccw hp hab hbd) (o3_of_ccw hp hac hcd)
    (o3_of_ccw hp hbc hcd)
    (cone_at hn hinj hp (ne_of_gt had) (ne_of_gt hab) ha)
    (cone_at hn hinj hp (ne_of_lt hab) (ne_of_gt hbc) hb)
    (cone_at hn hinj hp (ne_of_lt hbc) (ne_of_gt hcd) hc)
    (cone_at hn hinj hp (ne_of_lt hcd) (ne_of_lt had) hd)

theorem acute_ok (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ acuteCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [acuteCls, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with ⟨v, -, s, hs, hc⟩ | ⟨S, hS, rfl⟩
  · obtain ⟨hpv, hnx, -, -⟩ := nb_facts hn v
    have hA : len p (cp (pv n v) (nx n v)) ≤ len p s → asg p (.A v) = true := by
      intro hle
      rw [asg_A, decide_eq_true_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rw [len_cp] at hle
      rcases hs with rfl | rfl <;> rw [len_cp] at hle
      · exact acute_of_le_left (fun h => hnx (hinj h).symm) (d2_le_of_dist_le hle)
      · exact acute_of_le_right (fun h => hpv (hinj h)) (d2_le_of_dist_le hle)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_Eq']
      by_cases h : len p (cp (pv n v) (nx n v)) = len p s
      · simp [hA h.le]
      · simp [h]
    · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_L]
      by_cases h : len p (cp (pv n v) (nx n v)) < len p s
      · simp [hA h.le]
      · simp [h]
  · obtain ⟨hsub, hlen⟩ := mem_subsets hS
    have hpw : S.Pairwise (· < ·) := (List.pairwise_lt_finRange n).sublist hsub
    match S, hlen, hpw with
    | [a, b, c, d], _, hpw =>
      have hab : a < b := List.rel_of_pairwise_cons hpw (by simp)
      have hbc : b < c := List.rel_of_pairwise_cons hpw.of_cons (by simp)
      have hcd : c < d := List.rel_of_pairwise_cons hpw.of_cons.of_cons (by simp)
      simp only [List.map_cons, List.map_nil, CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
        asg_A]
      by_cases ha : acute p a
      · by_cases hb : acute p b
        · by_cases hc : acute p c
          · by_cases hd : acute p d
            · exact (no_four_acute hn hinj hp hab hbc hcd ha hb hc hd).elim
            · simp [hd]
          · simp [hc]
        · simp [hb]
      · simp [ha]

theorem genA_eval {K : Nat} (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p)
    (hK : ∀ v : Fin n, {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}.ncard < K + 1) :
    (genA n K).eval (asg p) = true := by
  simp only [genA, CNF.eval, List.all_toArray, List.all_append, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨eqv_ok, ord_ok⟩, class_ok hK⟩, side_ok hinj hp⟩, acute_ok hn hinj hp⟩

end E982C
