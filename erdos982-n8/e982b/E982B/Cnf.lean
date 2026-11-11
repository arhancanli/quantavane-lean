/-
Erdős Problem #982, case n = 8: the finite check as a CNF over structured atoms, and its refutation.

Vertices are `Fin 8`, in the cyclic order of the polygon. Atoms:
  `e v u w`  vertex v is equidistant from u and w (u < w)
  `E P Q`    the vertex pairs P and Q (each stored as (min, max)) have equal length
  `L P Q`    the pair P is strictly shorter than the pair Q
Clause families (see erdos982_patterns.c and E982/Gen.lean for the lemmas):
  link, transitivity of E, at most three distances per vertex, Lemma 1 (apexes), strict order, Lemma 3 (sides).
`gen` is `genA` relabelled to `Nat`; `gen_unsat` refutes it with an LRAT certificate checked by Lean's verified
LRAT checker (evaluated by `native_decide`); `genA_unsat` transfers this to every assignment of the atoms.
-/
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

namespace E982B

inductive Atom where
  | e : Fin 8 → Fin 8 → Fin 8 → Atom
  | E : Fin 8 × Fin 8 → Fin 8 × Fin 8 → Atom
  | L : Fin 8 × Fin 8 → Fin 8 × Fin 8 → Atom
  deriving DecidableEq

def code (P : Fin 8 × Fin 8) : Nat := P.1.val * 8 + P.2.val

def enc : Atom → Nat
  | .e v u w => v.val * 64 + u.val * 8 + w.val
  | .E P Q => 512 + code P * 64 + code Q
  | .L P Q => 4608 + code P * 64 + code Q

def f8 (k : Nat) : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by decide)⟩

def dec (x : Nat) : Atom :=
  if x < 512 then .e (f8 (x / 64)) (f8 (x / 8)) (f8 x)
  else if x < 4608 then
    let y := x - 512
    .E (f8 (y / 512), f8 (y / 64)) (f8 (y / 8), f8 y)
  else
    let y := x - 4608
    .L (f8 (y / 512), f8 (y / 64)) (f8 (y / 8), f8 y)

theorem dec_enc_e : ∀ v u w : Fin 8, dec (enc (.e v u w)) = .e v u w := by decide
theorem dec_enc_E : ∀ a b c d : Fin 8, dec (enc (.E (a, b) (c, d))) = .E (a, b) (c, d) := by decide
theorem dec_enc_L : ∀ a b c d : Fin 8, dec (enc (.L (a, b) (c, d))) = .L (a, b) (c, d) := by decide

theorem dec_enc (x : Atom) : dec (enc x) = x := by
  rcases x with ⟨v, u, w⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩
  · exact dec_enc_e v u w
  · exact dec_enc_E a b c d
  · exact dec_enc_L a b c d

/-! Index combinatorics on the 8-cycle. -/

/-- `x` lies strictly inside the counterclockwise arc from `a` to `b`. -/
def arcIn (x a b : Fin 8) : Bool :=
  let dx := (x.val + 8 - a.val) % 8
  let db := (b.val + 8 - a.val) % 8
  0 < dx && dx < db

def isEdge (u w : Fin 8) : Bool :=
  let d := (u.val + 8 - w.val) % 8
  d == 1 || d == 7

def cp (u w : Fin 8) : Fin 8 × Fin 8 := if u < w then (u, w) else (w, u)

/-- the equality atom of two pairs, in a canonical order -/
def Eq' (P Q : Fin 8 × Fin 8) : Atom := if code P < code Q then .E P Q else .E Q P

def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

def subsets {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (subsets k xs).map (x :: ·) ++ subsets (k + 1) xs

def vs : List (Fin 8) := List.finRange 8
def prs : List (Fin 8 × Fin 8) := pairsOf vs
def cands (u w : Fin 8) : List (Fin 8) := vs.filter fun v => v != u && v != w

/-! Clause families. -/

def linkCls : List (CNF.Clause Atom) :=
  vs.flatMap fun v => prs.flatMap fun (u, w) =>
    if v != u && v != w then
      [[(.e v u w, false), (Eq' (cp v u) (cp v w), true)], [(.e v u w, true), (Eq' (cp v u) (cp v w), false)]]
    else []

def transCls : List (CNF.Clause Atom) :=
  prs.flatMap fun P => prs.flatMap fun Q => prs.flatMap fun R =>
    if P != Q && Q != R && P != R then [[(Eq' P Q, false), (Eq' Q R, false), (Eq' P R, true)]] else []

def classCls : List (CNF.Clause Atom) :=
  vs.flatMap fun v => (subsets 4 (vs.filter (· != v))).map fun S =>
    (pairsOf S).map fun (a, b) => (.e v a b, true)

def l1Cls : List (CNF.Clause Atom) :=
  prs.flatMap fun (u, w) => (pairsOf (cands u w)).flatMap fun (v1, v2) =>
    if isEdge u w || arcIn v1 u w == arcIn v2 u w then [[(.e v1 u w, false), (.e v2 u w, false)]] else []

def orderCls : List (CNF.Clause Atom) :=
  (prs.flatMap fun P => prs.flatMap fun Q =>
    if P != Q then [[(Eq' P Q, false), (.L P Q, false)]] else []) ++
  (prs.flatMap fun P => prs.flatMap fun Q => prs.flatMap fun R =>
    if P != Q && Q != R && P != R then
      [[(.L P Q, false), (.L Q R, false), (.L P R, true)],
       [(Eq' P Q, false), (.L Q R, false), (.L P R, true)],
       [(.L P Q, false), (Eq' Q R, false), (.L P R, true)]]
    else [])

/-- for the edge {u, w}: the endpoint `i` with `w = i + 1` or `u = i + 1` -/
def edgeStart (u w : Fin 8) : Fin 8 := if (w.val + 8 - u.val) % 8 == 1 then u else w

def l3Cls : List (CNF.Clause Atom) :=
  prs.flatMap fun (u, w) =>
    if isEdge u w then
      let i := edgeStart u w
      let j := i + 1
      (cands u w).flatMap fun a => vs.flatMap fun x =>
        if x != i && x != j && x != a then
          let near := if arcIn x j a then j else i
          let far := if arcIn x j a then i else j
          [[(.e a u w, false), (.L (cp x near) (cp x far), true)]]
        else []
    else
      (pairsOf (cands u w)).flatMap fun (a, b) =>
        if arcIn a u w != arcIn b u w then
          vs.flatMap fun x =>
            if x != u && x != w && x != a && x != b then
              let near := if arcIn x a b == arcIn u a b then u else w
              let far := if arcIn x a b == arcIn u a b then w else u
              [[(.e a u w, false), (.e b u w, false), (.L (cp x near) (cp x far), true)]]
            else []
        else []

def genA : CNF Atom := ⟨(linkCls ++ transCls ++ classCls ++ l1Cls ++ orderCls ++ l3Cls).toArray⟩

def gen : CNF Nat := genA.relabel enc

end E982B
