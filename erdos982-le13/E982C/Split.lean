/-
Erdős #982: refuting a CNF `F` with an LRAT proof cut into chunks, so that each chunk is checked by its own
`native_decide` call with a bounded memory footprint. Chunk `j < k` refutes `chunkCNF F S_{j-1} S_j`, that is
`F ∧ S_{j-1} ∧ (some clause of S_j is false)` (the last part as `negCls`, with fresh selector variables), so
`F ∧ S_{j-1} ⊨ S_j` (`chunk_sound`); the last chunk refutes `F ∧ S_{k-1}` (`last_sound`). The interface clause lists
`S_j` are arbitrary data (parsed from text): the lemmas hold for every list. Std-only module (no Mathlib).
-/
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

namespace E982C

/-- `max acc (1 + the largest variable of c)` -/
def clTop (acc : Nat) (c : CNF.Clause Nat) : Nat := c.foldl (fun m l => max m (l.1 + 1)) acc

/-- `max acc (1 + the largest variable of the clauses of L)` -/
def lsTop (acc : Nat) (L : List (CNF.Clause Nat)) : Nat := L.foldl clTop acc

theorem clTop_ge (c : CNF.Clause Nat) : ∀ acc, acc ≤ clTop acc c := by
  induction c with
  | nil => intro acc; simp [clTop]
  | cons l c ih =>
    intro acc
    have := ih (max acc (l.1 + 1))
    simp only [clTop, List.foldl_cons] at this ⊢
    omega

theorem clTop_lt (c : CNF.Clause Nat) : ∀ acc, ∀ l ∈ c, l.1 < clTop acc c := by
  induction c with
  | nil => intro acc l hl; simp at hl
  | cons l0 c ih =>
    intro acc l hl
    have h1 := clTop_ge c (max acc (l0.1 + 1))
    simp only [clTop, List.foldl_cons] at h1 ⊢
    rcases List.mem_cons.mp hl with rfl | hl
    · omega
    · exact ih _ l hl

theorem lsTop_ge (L : List (CNF.Clause Nat)) : ∀ acc, acc ≤ lsTop acc L := by
  induction L with
  | nil => intro acc; simp [lsTop]
  | cons c L ih =>
    intro acc
    have h1 := ih (clTop acc c)
    have h2 := clTop_ge c acc
    simp only [lsTop, List.foldl_cons] at h1 ⊢
    omega

theorem lsTop_lt (L : List (CNF.Clause Nat)) : ∀ acc, ∀ c ∈ L, ∀ l ∈ c, l.1 < lsTop acc L := by
  induction L with
  | nil => intro acc c hc; simp at hc
  | cons c0 L ih =>
    intro acc c hc l hl
    have h1 := lsTop_ge L (clTop acc c0)
    simp only [lsTop, List.foldl_cons] at h1 ⊢
    rcases List.mem_cons.mp hc with rfl | hc
    · have := clTop_lt c acc l hl
      omega
    · exact ih _ c hc l hl

/-- "some clause of `S` is false", with selector variable `b + i` for the clause `S[i]`: the clause
`s_0 ∨ s_1 ∨ ...` and, for each clause `S[i]` and literal `l` of it, the clause `¬ s_i ∨ ¬ l`. -/
def negCls (b : Nat) (S : List (CNF.Clause Nat)) : List (CNF.Clause Nat) :=
  ((List.range S.length).map fun i => (b + i, true)) ::
    S.zipIdx.flatMap fun (C, i) => C.map fun l => [(b + i, false), (l.1, !l.2)]

/-- The CNF refuted by a non-final chunk: `F`, then `Sp`, then `negCls b S` with `b` above every variable. -/
def chunkCNF (F : CNF Nat) (Sp S : List (CNF.Clause Nat)) : CNF Nat :=
  let G := F ++ ⟨Sp.toArray⟩
  G ++ ⟨(negCls (lsTop (lsTop 0 G.clauses.toList) S) S).toArray⟩

/-- The CNF refuted by the final chunk: `F`, then `Sp`. -/
def lastCNF (F : CNF Nat) (Sp : List (CNF.Clause Nat)) : CNF Nat := F ++ ⟨Sp.toArray⟩

theorem eval_list (a : Nat → Bool) (L : List (CNF.Clause Nat)) :
    CNF.eval a ⟨L.toArray⟩ = true ↔ ∀ c ∈ L, c.eval a = true := by
  simp [CNF.eval]

/-- A refuted non-final chunk: every assignment satisfying `F` and `Sp` satisfies `S`. -/
theorem chunk_sound (F : CNF Nat) (Sp S : List (CNF.Clause Nat)) (h : (chunkCNF F Sp S).Unsat)
    (a : Nat → Bool) (hF : F.eval a = true) (hSp : ∀ c ∈ Sp, c.eval a = true) :
    ∀ c ∈ S, c.eval a = true := by
  intro C hC
  cases hCe : C.eval a
  case true => rfl
  exfalso
  obtain ⟨i, hi, hCi⟩ := List.getElem_of_mem hC
  let G := F ++ (⟨Sp.toArray⟩ : CNF Nat)
  let b := lsTop (lsTop 0 G.clauses.toList) S
  have hGv : ∀ c ∈ G.clauses.toList, ∀ l ∈ c, l.1 < b := fun c hc l hl =>
    Nat.lt_of_lt_of_le (lsTop_lt _ 0 c hc l hl) (lsTop_ge _ _)
  have hSv : ∀ c ∈ S, ∀ l ∈ c, l.1 < b := lsTop_lt S _
  let a' : Nat → Bool := fun v => if v < b then a v else decide (v = b + i)
  have hG0 : G.eval a = true := by
    simp only [G, CNF.eval_append, hF, Bool.true_and]
    exact (eval_list a Sp).mpr hSp
  have hG : G.eval a' = true := by
    rw [CNF.eval_congr a' a G]
    · exact hG0
    · intro v hv
      obtain ⟨c, hc, hm⟩ := hv
      have hvb : v < b := by
        rcases hm with hm | hm
        · exact hGv c (Array.mem_toList_iff.mpr hc) _ hm
        · exact hGv c (Array.mem_toList_iff.mpr hc) _ hm
      simp [a', hvb]
  have hN : CNF.eval a' ⟨(negCls b S).toArray⟩ = true := by
    rw [eval_list]
    intro c hc
    simp only [negCls, List.mem_cons, List.mem_flatMap, List.mem_map] at hc
    rcases hc with rfl | ⟨⟨C', j⟩, hj, l, hl, rfl⟩
    · simp only [CNF.Clause.eval, List.any_map, List.any_eq_true, List.mem_range]
      refine ⟨i, hi, ?_⟩
      simp [a']
    · by_cases hji : j = i
      · subst hji
        have hC' : S[j]? = some C' := List.mem_zipIdx_iff_getElem?.mp hj
        rw [List.getElem?_eq_getElem hi, Option.some.injEq, hCi] at hC'
        subst hC'
        have hlb := hSv _ hC l hl
        have hl' : (a l.1 == l.2) = false := by
          have := hCe
          simp only [CNF.Clause.eval, List.any_eq_false] at this
          simpa using this l hl
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
        have : a' l.1 = a l.1 := by simp [a', hlb]
        rw [this]
        cases h1 : a l.1 <;> cases h2 : l.2 <;> simp_all
      · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
        have hnb : ¬ (b + j < b) := by omega
        have : a' (b + j) = false := by simp [a', hnb, hji]
        simp [this]
  have h1 : CNF.eval a' (G ++ ⟨(negCls b S).toArray⟩) = false := h a'
  rw [CNF.eval_append, hG, hN] at h1
  exact Bool.noConfusion h1

/-- A refuted final chunk: no assignment satisfies both `F` and `Sp`. -/
theorem last_sound (F : CNF Nat) (Sp : List (CNF.Clause Nat)) (h : (lastCNF F Sp).Unsat)
    (a : Nat → Bool) (hF : F.eval a = true) (hSp : ∀ c ∈ Sp, c.eval a = true) : False := by
  have h1 := h a
  simp only [lastCNF, CNF.eval_append, hF, Bool.true_and] at h1
  rw [(eval_list a Sp).mpr hSp] at h1
  exact Bool.noConfusion h1

/-- Parse clause lines `l1 l2 ... 0` (DIMACS literals: `k` is variable `|k| - 1`, positive iff `k > 0`). The parser
is not trusted: the soundness lemmas above hold for whatever list it returns. -/
def parseCls (s : String) : List (CNF.Clause Nat) := Id.run do
  let bs := s.toUTF8
  let mut out : Array (CNF.Clause Nat) := #[]
  let mut cur : Array (Nat × Bool) := #[]
  let mut num : Nat := 0
  let mut neg := false
  let mut innum := false
  for i in [0:bs.size] do
    let c := bs[i]!
    if c == 45 then
      neg := true
    else if 48 ≤ c && c ≤ 57 then
      num := num * 10 + (c.toNat - 48)
      innum := true
    else if innum then
      if num == 0 then
        out := out.push cur.toList
        cur := #[]
      else
        cur := cur.push (num - 1, !neg)
      num := 0
      neg := false
      innum := false
  return out.toList

def parseProof' (s : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]

end E982C
