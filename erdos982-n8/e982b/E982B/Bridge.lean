/-
Erdős #982, n = 8, Lean part B: the bridge. A strictly convex octagon (formal-conjectures' `IsCcwConvexPolygon`)
with at most three distinct distances at every vertex gives an assignment of the atoms satisfying every clause of
`genA`; `genA` is unsatisfiable (`genA_unsat`), so no such octagon exists.
-/
import E982B.Comb
import E982B.Unsat

open EuclideanGeometry Std.Sat

namespace E982B

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
      exact ⟨h1.cons₂ x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := mem_subsets h
      exact ⟨h1.cons x, h2⟩

theorem prs_lt : ∀ P ∈ prs, P.1 < P.2 := by decide

theorem vs_nodup : vs.Nodup := List.nodup_finRange 8

theorem mem_cands {u w v : Fin 8} : v ∈ cands u w ↔ v ≠ u ∧ v ≠ w := by
  simp [cands, vs, List.mem_finRange]

/-! The assignment given by a polygon. -/

variable (p : Fin 8 → ℝ²)

noncomputable def len (P : Fin 8 × Fin 8) : ℝ := dist (p P.1) (p P.2)

noncomputable def asg : Atom → Bool
  | .e v u w => decide (dist (p v) (p u) = dist (p v) (p w))
  | .E P Q => decide (len p P = len p Q)
  | .L P Q => decide (len p P < len p Q)

theorem len_cp (u w : Fin 8) : len p (cp u w) = dist (p u) (p w) := by
  unfold cp len; split <;> simp [dist_comm]

theorem asg_Eq' (P Q : Fin 8 × Fin 8) : asg p (Eq' P Q) = decide (len p P = len p Q) := by
  unfold Eq'; split
  · rfl
  · simp only [asg, eq_comm]

theorem asg_L (P Q : Fin 8 × Fin 8) : asg p (.L P Q) = decide (len p P < len p Q) := rfl

theorem asg_e (v u w : Fin 8) : asg p (.e v u w) = decide (dist (p v) (p u) = dist (p v) (p w)) := rfl

variable {p}

/-! Each clause family is satisfied. -/

theorem link_ok : ∀ c ∈ linkCls, c.eval (asg p) = true := by
  intro c hc
  simp only [linkCls, List.mem_flatMap] at hc
  obtain ⟨v, -, ⟨u, w⟩, -, hc⟩ := hc
  split_ifs at hc with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have key : asg p (Eq' (cp v u) (cp v w)) = asg p (.e v u w) := by
      rw [asg_Eq', len_cp, len_cp]; rfl
    rcases hc with rfl | rfl <;>
      simp [CNF.Clause.eval, key] <;> cases asg p (.e v u w) <;> simp
  · simp at hc

theorem trans_ok : ∀ c ∈ transCls, c.eval (asg p) = true := by
  intro c hc
  simp only [transCls, List.mem_flatMap] at hc
  obtain ⟨P, -, Q, -, R, -, hc⟩ := hc
  split_ifs at hc with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', Bool.or_false]
    by_cases h1 : len p P = len p Q <;> by_cases h2 : len p Q = len p R <;> simp [h1, h2] <;> linarith
  · simp at hc

theorem order_ok : ∀ c ∈ orderCls, c.eval (asg p) = true := by
  intro c hc
  simp only [orderCls, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨P, -, Q, -, hc⟩ | ⟨P, -, Q, -, R, -, hc⟩
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', asg_L, Bool.or_false]
      by_cases h1 : len p P = len p Q <;> simp [h1]
    · simp at hc
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', asg_L, Bool.or_false]
      · by_cases h1 : len p P < len p Q <;> by_cases h2 : len p Q < len p R <;> simp [h1, h2] <;> linarith
      · by_cases h1 : len p P = len p Q <;> by_cases h2 : len p Q < len p R <;> simp [h1, h2] <;> linarith
      · by_cases h1 : len p P < len p Q <;> by_cases h2 : len p Q = len p R <;> simp [h1, h2] <;> linarith
    · simp at hc

theorem class_ok (hK : ∀ v : Fin 8, {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (p v) (p j)}.ncard < 4) :
    ∀ c ∈ classCls, c.eval (asg p) = true := by
  intro c hc
  simp only [classCls, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨v, -, S, hS, rfl⟩ := hc
  obtain ⟨hsub, hlen⟩ := mem_subsets hS
  have hnd : S.Nodup := (vs_nodup.filter _).sublist hsub
  have hne : ∀ j ∈ S, j ≠ v := fun j hj => by
    have := hsub.subset hj
    simp only [List.mem_filter, bne_iff_ne] at this
    exact this.2
  set D := {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (p v) (p j)} with hDdef
  have hDfin : D.Finite := by
    have : D ⊆ Set.range (fun j : Fin 8 => dist (p v) (p j)) := by
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
  · exact ⟨(x, y), h, by simp [asg_e, heq]⟩
  · exact ⟨(y, x), h, by simp [asg_e, heq]⟩

theorem l1_ok (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ l1Cls, c.eval (asg p) = true := by
  intro c hc
  simp only [l1Cls, List.mem_flatMap] at hc
  obtain ⟨⟨u, w⟩, huw, ⟨v1, v2⟩, hv, hc⟩ := hc
  split_ifs at hc with hcond
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    have huw' : u ≠ w := ne_of_lt (prs_lt _ huw)
    obtain ⟨hv1, hv2, hnd⟩ := mem_pairsOf hv
    have hv12 : v1 ≠ v2 := hnd (vs_nodup.filter _)
    rw [mem_cands] at hv1 hv2
    simp only [CNF.Clause.eval, List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : dist (p v1) (p u) = dist (p v1) (p w)
    · by_cases h2 : dist (p v2) (p u) = dist (p v2) (p w)
      · exfalso
        have hpuw : p u ≠ p w := fun h => huw' (hinj h)
        have hsum := o3_add_eq_zero hpuw ((dist_eq_iff_d2 _ _ _ _).mp h1) ((dist_eq_iff_d2 _ _ _ _).mp h2)
        have hcs := comb_l1 u w v1 v2 huw' hv12 hv1.1 hv1.2 hv2.1 hv2.2 hcond
        have o1 := orient hp hv12 hv2.1 hv1.1
        have o2 := orient hp hv12 hv2.2 hv1.2
        cases hc' : csign v1 v2 u
        · have a1 := o1.2 hc'
          have a2 := o2.2 (by rw [← hcs]; exact hc')
          linarith
        · have a1 := o1.1 hc'
          have a2 := o2.1 (by rw [← hcs]; exact hc')
          linarith
      · exact ⟨_, Or.inr rfl, by simp [asg_e, h2]⟩
    · exact ⟨_, Or.inl rfl, by simp [asg_e, h1]⟩
  · simp at hc

theorem l3_ok (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ l3Cls, c.eval (asg p) = true := by
  intro c hc
  simp only [l3Cls, List.mem_flatMap] at hc
  obtain ⟨⟨u, w⟩, huw, hc⟩ := hc
  have huw' : u ≠ w := ne_of_lt (prs_lt _ huw)
  have hpuw : p u ≠ p w := fun h => huw' (hinj h)
  split_ifs at hc with hedge
  · -- an edge {u, w} with apex a
    simp only [List.mem_flatMap] at hc
    obtain ⟨a, ha, x, -, hc⟩ := hc
    rw [mem_cands] at ha
    by_cases hx : (x != edgeStart u w && x != edgeStart u w + 1 && x != a) = true
    · simp only [hx, if_true, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
      obtain ⟨⟨hxi, hxj⟩, hxa⟩ := hx
      have hends := comb_edge_ends u w huw' hedge
      set i := edgeStart u w with hidef
      have hai : a ≠ i := by
        rcases hends with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1]
        · exact ha.1
        · exact ha.2
      have haj : a ≠ i + 1 := by
        rcases hends with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2]
        · exact ha.2
        · exact ha.1
      have hij : i ≠ i + 1 := by
        rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e2, e1]
        · exact huw'
        · exact huw'.symm
      have hpij : p i ≠ p (i + 1) := fun h => hij (hinj h)
      have oij := orient hp hai hij haj
      have oix := orient hp hai (Ne.symm hxi) (Ne.symm hxa)
      have ojx := orient hp haj (Ne.symm hxj) (Ne.symm hxa)
      have hcb := comb_l3e i a x hai haj hxi hxj hxa
      have hne : o3 (p a) (p i) (p (i + 1)) ≠ 0 := by
        cases hs : csign a i (i + 1)
        · exact (oij.2 hs).ne
        · exact (oij.1 hs).ne'
      simp only [CNF.Clause.eval, List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false]
      by_cases h1 : dist (p a) (p u) = dist (p a) (p w)
      · refine ⟨_, Or.inr rfl, ?_⟩
        simp only [asg_L, len_cp, beq_iff_eq, decide_eq_true_eq]
        have hd : d2 (p a) (p i) = d2 (p a) (p (i + 1)) := by
          rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e2, e1]
          · exact (dist_eq_iff_d2 _ _ _ _).mp h1
          · exact ((dist_eq_iff_d2 _ _ _ _).mp h1).symm
        by_cases harc : arcIn x (i + 1) a = true
        · obtain ⟨c1, c2⟩ := hcb.1 harc
          rw [if_pos harc, if_pos harc, dist_lt_iff_d2]
          apply side_edge hpij hd hne
          cases hs : csign a i (i + 1)
          · right; exact ⟨oix.2 (c1.trans hs), ojx.2 (c2.trans hs), oij.2 hs⟩
          · left; exact ⟨oix.1 (c1.trans hs), ojx.1 (c2.trans hs), oij.1 hs⟩
        · have harc' : arcIn x (i + 1) a = false := by simpa using harc
          obtain ⟨c1, c2⟩ := hcb.2 harc'
          rw [if_neg harc, if_neg harc, dist_lt_iff_d2]
          have hne' : o3 (p a) (p (i + 1)) (p i) ≠ 0 := by rw [o3_swap]; exact neg_ne_zero.mpr hne
          apply side_edge hpij.symm hd.symm hne'
          have sw := o3_swap (p a) (p i) (p (i + 1))
          cases hs : csign a i (i + 1)
          · left
            have e1 : csign a i x = true := by
              cases h' : csign a i x
              · exact absurd (h'.trans hs.symm) c1
              · rfl
            have e2 : csign a (i + 1) x = true := by
              cases h' : csign a (i + 1) x
              · exact absurd (h'.trans hs.symm) c2
              · rfl
            exact ⟨ojx.1 e2, oix.1 e1, by have := oij.2 hs; linarith⟩
          · right
            have e1 : csign a i x = false := by
              cases h' : csign a i x
              · rfl
              · exact absurd (h'.trans hs.symm) c1
            have e2 : csign a (i + 1) x = false := by
              cases h' : csign a (i + 1) x
              · rfl
              · exact absurd (h'.trans hs.symm) c2
            exact ⟨ojx.2 e2, oix.2 e1, by have := oij.1 hs; linarith⟩
      · exact ⟨_, Or.inl rfl, by simp [asg_e, h1]⟩
    · simp only [hx, if_false, Bool.false_eq_true] at hc
      simp at hc
  · -- a diagonal {u, w} with apexes a, b
    simp only [List.mem_flatMap] at hc
    obtain ⟨⟨a, b⟩, hab, hc⟩ := hc
    by_cases hside : (arcIn a u w != arcIn b u w) = true
    · simp only [hside, if_true, List.mem_flatMap] at hc
      obtain ⟨x, -, hc⟩ := hc
      by_cases hx : (x != u && x != w && x != a && x != b) = true
      · simp only [hx, if_true, List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        obtain ⟨ha, hb, hnd⟩ := mem_pairsOf hab
        have hab' : a ≠ b := hnd (vs_nodup.filter _)
        rw [mem_cands] at ha hb
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
        obtain ⟨⟨⟨hxu, hxw⟩, hxa⟩, hxb⟩ := hx
        have hside' : arcIn a u w ≠ arcIn b u w := by simpa using hside
        have hcb := comb_l3d u w a b x huw' hab' ha.1 ha.2 hb.1 hb.2 hxu hxw hxa hxb hside'
        have hpab : p a ≠ p b := fun h => hab' (hinj h)
        simp only [CNF.Clause.eval, List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false]
        by_cases h1 : dist (p a) (p u) = dist (p a) (p w)
        · by_cases h2 : dist (p b) (p u) = dist (p b) (p w)
          · refine ⟨_, Or.inr (Or.inr rfl), ?_⟩
            simp only [asg_L, len_cp, beq_iff_eq, decide_eq_true_eq]
            have ha2 := (dist_eq_iff_d2 _ _ _ _).mp h1
            have hb2 := (dist_eq_iff_d2 _ _ _ _).mp h2
            have obx := orient hp hab' (Ne.symm hxb) (Ne.symm hxa)
            by_cases hsame : (arcIn x a b == arcIn u a b) = true
            · have cs := hcb.1 hsame
              have obu := orient hp hab' hb.1 ha.1
              have hs' : arcIn x a b = arcIn u a b := beq_iff_eq.mp hsame
              rw [if_pos hs', if_pos hs', dist_lt_iff_d2]
              apply side_diag hpab hpuw ha2 hb2
              cases hs : csign a b u
              · right; exact ⟨obx.2 (cs.trans hs), obu.2 hs⟩
              · left; exact ⟨obx.1 (cs.trans hs), obu.1 hs⟩
            · have hsame' : (arcIn x a b == arcIn u a b) = false := by simpa using hsame
              have cs := hcb.2 hsame'
              have obw := orient hp hab' hb.2 ha.2
              have hs' : ¬ arcIn x a b = arcIn u a b := fun h => hsame (beq_iff_eq.mpr h)
              rw [if_neg hs', if_neg hs', dist_lt_iff_d2]
              apply side_diag hpab hpuw.symm ha2.symm hb2.symm
              cases hs : csign a b w
              · right; exact ⟨obx.2 (cs.trans hs), obw.2 hs⟩
              · left; exact ⟨obx.1 (cs.trans hs), obw.1 hs⟩
          · exact ⟨_, Or.inr (Or.inl rfl), by simp [asg_e, h2]⟩
        · exact ⟨_, Or.inl rfl, by simp [asg_e, h1]⟩
      · simp only [hx, if_false, Bool.false_eq_true] at hc
        simp at hc
    · simp only [hside, if_false, Bool.false_eq_true] at hc
      simp at hc

theorem genA_eval (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p)
    (hK : ∀ v : Fin 8, {d : ℝ | ∃ j : Fin 8, j ≠ v ∧ d = dist (p v) (p j)}.ncard < 4) :
    genA.eval (asg p) = true := by
  simp only [genA, CNF.eval, List.all_toArray, List.all_append, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨link_ok, trans_ok⟩, class_ok hK⟩, l1_ok hinj hp⟩, order_ok⟩, l3_ok hinj hp⟩


end E982B
