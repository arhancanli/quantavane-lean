/-
Erdős Problem #982, the case n = 8: the CNF of the finite check, generated in Lean from the three lemmas.

Vertices 0, ..., n-1 of a strictly convex polygon in counterclockwise order. Atoms:
  e v u w : vertex v is equidistant from u and w ("v is an apex of {u, w}")
  E p q   : the pairs p and q (vertex pairs, coded u * n + w with u < w) have equal length
  L p q   : pair p is strictly shorter than pair q
Clauses:
  link    e v u w ↔ E {v,u} {v,w}
  E       transitive (with E symmetric by construction)
  classes every K + 1 of the other vertices of v contain an equidistant pair (at most K distances at v)
  Lemma 1 an edge has at most one apex; two apexes of a diagonal lie in different open arcs between its ends
  order   L transitive and irreflexive on values: E p q → ¬ L p q; L respects E on both sides
  Lemma 3 a diagonal uw with apexes a, b in different arcs: every other x is strictly nearer to the end of uw in
          its own arc between a and b; an edge {i, i+1} with apex a: x strictly inside the ccw arc (i+1, a) is
          nearer to i+1, the other x nearer to i.
-/
import Std.Sat.CNF

open Std.Sat

namespace E982

/-- `x` lies strictly inside the counterclockwise arc from `a` to `b` (vertices mod `n`). -/
def arcIn (n x a b : Nat) : Bool :=
  let dx := (x + n - a) % n
  let db := (b + n - a) % n
  0 < dx && dx < db

/-- `u` and `w` are adjacent vertices. -/
def isEdge (n u w : Nat) : Bool :=
  let d := (u + n - w) % n
  d == 1 || d == n - 1

/-- code of the unordered pair {u, w} -/
def pc (n u w : Nat) : Nat := if u < w then u * n + w else w * n + u

def eVar (n v u w : Nat) : Nat := v * (n * n) + pc n u w
def EVar (n p q : Nat) : Nat := n * n * n + (if p < q then p * (n * n) + q else q * (n * n) + p)
def LVar (n p q : Nat) : Nat := n * n * n + n * n * n * n + p * (n * n) + q

def pos (a : Nat) : Literal Nat := (a, true)
def neg (a : Nat) : Literal Nat := (a, false)

/-- ordered pairs (x, y) with x before y in the list -/
def pairsOf : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

/-- all sublists of length k -/
def subsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (subsets k xs).map (x :: ·) ++ subsets (k + 1) xs

def gen (n K : Nat) : CNF Nat := Id.run do
  let vs := List.range n
  let ps := pairsOf vs
  let pcs := ps.map fun (u, w) => pc n u w
  let mut cls : Array (CNF.Clause Nat) := #[]
  -- link
  for v in vs do
    for (u, w) in ps do
      if u != v && w != v then
        let e := eVar n v u w
        let E := EVar n (pc n v u) (pc n v w)
        cls := cls.push [neg e, pos E]
        cls := cls.push [pos e, neg E]
  -- E transitive
  for p in pcs do
    for q in pcs do
      for r in pcs do
        if p != q && q != r && p != r then
          cls := cls.push [neg (EVar n p q), neg (EVar n q r), pos (EVar n p r)]
  -- at most K distinct distances at each vertex
  for v in vs do
    for S in subsets (K + 1) (vs.filter (· != v)) do
      cls := cls.push ((pairsOf S).map fun (a, b) => pos (eVar n v a b))
  -- Lemma 1
  for (u, w) in ps do
    let cands := vs.filter fun v => v != u && v != w
    for (v1, v2) in pairsOf cands do
      if isEdge n u w || arcIn n v1 u w == arcIn n v2 u w then
        cls := cls.push [neg (eVar n v1 u w), neg (eVar n v2 u w)]
  -- strict order compatible with the equalities
  for p in pcs do
    for q in pcs do
      if p != q then
        cls := cls.push [neg (EVar n p q), neg (LVar n p q)]
  for p in pcs do
    for q in pcs do
      for r in pcs do
        if p != q && q != r && p != r then
          cls := cls.push [neg (LVar n p q), neg (LVar n q r), pos (LVar n p r)]
          cls := cls.push [neg (EVar n p q), neg (LVar n q r), pos (LVar n p r)]
          cls := cls.push [neg (LVar n p q), neg (EVar n q r), pos (LVar n p r)]
  -- Lemma 3
  for (u, w) in ps do
    let cands := vs.filter fun v => v != u && v != w
    if isEdge n u w then
      let i := if (w + n - u) % n == 1 then u else w
      let j := (i + 1) % n
      for a in cands do
        for x in vs do
          if x != i && x != j && x != a then
            let near := if arcIn n x j a then j else i
            let far := if near == j then i else j
            cls := cls.push [neg (eVar n a u w), pos (LVar n (pc n x near) (pc n x far))]
    else
      for (a, b) in pairsOf cands do
        if arcIn n a u w != arcIn n b u w then
          for x in vs do
            if x != u && x != w && x != a && x != b then
              let near := if arcIn n x a b == arcIn n u a b then u else w
              let far := if near == u then w else u
              cls := cls.push [neg (eVar n a u w), neg (eVar n b u w),
                pos (LVar n (pc n x near) (pc n x far))]
  return ⟨cls⟩

end E982
