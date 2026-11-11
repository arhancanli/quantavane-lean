/-
Erdős Problem #982, round 2: the finite check for a general number `n` of vertices, as a CNF over structured
atoms, with at most `K` distinct distances at every vertex.

Vertices are `Fin n`, in the cyclic order of the polygon. Atoms:
  `E P Q`  the vertex pairs `P` and `Q` (each stored as (min, max)) have equal length
  `L P Q`  the pair `P` is strictly shorter than the pair `Q`
  `A v`    the interior angle at `v` is acute
Clause families:
  `eqvCls`    equal length is transitive
  `ordCls`    strict order: irreflexive on equal lengths, total, transitive
  `classCls`  at most `K` distinct distances at each vertex (every `K + 1` other vertices contain an equidistant pair)
  `sideCls`   half-plane rule: if `z` is not farther from `u` than from `w`, every vertex strictly inside the boundary
              arc from `u` to `z` that avoids `w` is strictly nearer to `u` than to `w`
  `acuteCls`  the angle at `v` is acute if `|v-1, v+1| <= |v-1, v|` or `<= |v, v+1|`; no four angles are acute
`gen n K` is `genA n K` relabelled to `Nat` by an injective code `enc`.
-/
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

namespace E982C

inductive Atom (n : Nat) where
  | E : Fin n × Fin n → Fin n × Fin n → Atom n
  | L : Fin n × Fin n → Fin n × Fin n → Atom n
  | A : Fin n → Atom n
  deriving DecidableEq

section Code

variable {n : Nat}

def code (P : Fin n × Fin n) : Nat := P.1.val * n + P.2.val

def enc : Atom n → Nat
  | .E P Q => code P * (n * n) + code Q
  | .L P Q => n * n * (n * n) + (code P * (n * n) + code Q)
  | .A v => 2 * (n * n * (n * n)) + v.val

variable [NeZero n]

theorem n_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

def fm (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ n_pos⟩

def decP (k : Nat) : Fin n × Fin n := (fm (k / n), fm k)

def dec (x : Nat) : Atom n :=
  if x < n * n * (n * n) then .E (decP (x / (n * n))) (decP (x % (n * n)))
  else if x < 2 * (n * n * (n * n)) then
    .L (decP ((x - n * n * (n * n)) / (n * n))) (decP ((x - n * n * (n * n)) % (n * n)))
  else .A (fm (x - 2 * (n * n * (n * n))))

end Code

/-! Index combinatorics on the `n`-cycle. -/

section Comb

variable {n : Nat}

/-- `(a, b, c)` is in strict cyclic (counterclockwise index) order. -/
def cycB (a b c : Fin n) : Bool :=
  (decide (a.val < b.val) && decide (b.val < c.val)) || (decide (b.val < c.val) && decide (c.val < a.val)) ||
    (decide (c.val < a.val) && decide (a.val < b.val))

/-- `y` lies strictly inside the boundary arc from `u` to `z` that avoids `w`. -/
def btwB (u y z w : Fin n) : Bool := (cycB u y z && cycB u z w) || (cycB w z y && cycB w y u)

def cp (u w : Fin n) : Fin n × Fin n := if u < w then (u, w) else (w, u)

/-- the equality atom of two pairs, in a canonical order -/
def Eq' (P Q : Fin n × Fin n) : Atom n := if code P < code Q then .E P Q else .E Q P

def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

def subsets {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (subsets k xs).map (x :: ·) ++ subsets (k + 1) xs

def vs (n : Nat) : List (Fin n) := List.finRange n
def prs (n : Nat) : List (Fin n × Fin n) := pairsOf (vs n)
def others (v : Fin n) : List (Fin n) := (vs n).filter (· != v)

end Comb

/-! Clause families. -/

section Clauses

variable (n : Nat)

def eqvCls : List (CNF.Clause (Atom n)) :=
  (prs n).flatMap fun P => (prs n).flatMap fun Q => (prs n).flatMap fun R =>
    if P != Q && Q != R && P != R then [[(Eq' P Q, false), (Eq' Q R, false), (Eq' P R, true)]] else []

def ordCls : List (CNF.Clause (Atom n)) :=
  ((prs n).flatMap fun P => (prs n).flatMap fun Q =>
    if P != Q then [[(Eq' P Q, false), (.L P Q, false)], [(Eq' P Q, true), (.L P Q, true), (.L Q P, true)]]
    else []) ++
  ((prs n).flatMap fun P => (prs n).flatMap fun Q => (prs n).flatMap fun R =>
    if P != Q && Q != R && P != R then [[(.L P Q, false), (.L Q R, false), (.L P R, true)]] else [])

def classCls (K : Nat) : List (CNF.Clause (Atom n)) :=
  (vs n).flatMap fun v => (subsets (K + 1) (others v)).map fun S =>
    (pairsOf S).map fun (a, b) => (Eq' (cp v a) (cp v b), true)

def sideCls : List (CNF.Clause (Atom n)) :=
  (vs n).flatMap fun u => (vs n).flatMap fun w => (vs n).flatMap fun z => (vs n).flatMap fun y =>
    if btwB u y z w then [[(.L (cp z w) (cp z u), true), (.L (cp y u) (cp y w), true)]] else []

variable [NeZero n]

def nx (v : Fin n) : Fin n := fm (v.val + 1)
def pv (v : Fin n) : Fin n := fm (v.val + n - 1)

def acuteCls : List (CNF.Clause (Atom n)) :=
  ((vs n).flatMap fun v =>
    [cp (pv n v) v, cp v (nx n v)].flatMap fun s =>
      [[(Eq' (cp (pv n v) (nx n v)) s, false), (.A v, true)], [(.L (cp (pv n v) (nx n v)) s, false), (.A v, true)]]) ++
  ((subsets 4 (vs n)).map fun S => S.map fun v => (.A v, false))

def genA (K : Nat) : CNF (Atom n) :=
  ⟨(eqvCls n ++ ordCls n ++ classCls n K ++ sideCls n ++ acuteCls n).toArray⟩

def gen (K : Nat) : CNF Nat := (genA n K).relabel enc

end Clauses

end E982C
