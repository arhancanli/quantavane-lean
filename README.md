# Lean proofs from Quantavane

Formal proofs, in Lean 4, of results found by Quantavane. Each folder is a Lake project (or two) that builds on its
own, with the exact versions pinned.

## Prior work on Erdős Problem #982 (added 12 Nov 2026)

The cases proved here were settled before this repository: n = 8 in print by Fishburn ("Distances in convex
polygons", in *The Mathematics of Paul Erdős I*, Springer, Theorem 3), and every n up to 13 by computer in
[Paulee314/erdos982](https://github.com/Paulee314/erdos982) (2 Nov 2026; proofs on Zenodo,
[doi:10.5281/zenodo.23880465](https://doi.org/10.5281/zenodo.23880465)), with solver proofs checked by the verified
checker cake_lpr. What this repository adds is a proof of those cases in Lean, in the form that
formal-conjectures states the problem. We found the earlier work after publishing; this note corrects our first
description of the cases as new.

## Erdős Problem #982, the case n = 8 (`erdos982-n8/`)

Erdős Problem #982 asks whether every convex polygon with n vertices has a vertex with at least floor(n/2) distinct
distances to the other vertices. This folder proves the case n = 8 in the form that
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states the problem (`Erdos982.erdos_982`
with n = 8): every strictly convex octagon, in either orientation, has a vertex with at least 4 distinct distances to
the other seven. The regular octagon shows that 4 cannot be raised. This is one case, not the whole problem.

```lean
theorem E982B.erdos_982_eight (p : Fin 8 → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin 8), { d : ℝ | ∃ j : Fin 8, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 8 / 2
```

How the proof goes:
- `e982b/E982B/Geom.lean`, `Comb.lean`: three lemmas from the signs of orientation determinants. (1) The vertices
  equidistant from two vertices u and w lie on their perpendicular bisector, so at most one lies on each arc between
  u and w. (2) Equality of lengths is transitive. (3) When both points where the bisector leaves the polygon are known,
  every other vertex is strictly nearer the endpoint on its side.
- `e982b/E982B/Bridge.lean`: an octagon with at most three distinct distances at every vertex gives an assignment of
  the atoms (which vertex is equidistant from which pair, which pairs have equal length, which is shorter) that
  satisfies every clause of a finite CNF built from the three lemmas (`e982b/E982B/Cnf.lean`, `e982/E982/Gen.lean`).
- `e982b/E982B/Unsat.lean`, `e982/E982/Lrat.lean`: the CNF is unsatisfiable. The certificate is an LRAT proof
  (`lrat/`, 733,062 bytes each; CaDiCaL 1.5.3 DRAT, converted to LRAT) checked by Lean's verified LRAT checker
  (`Std.Tactic.BVDecide.LRAT.check` with its soundness theorem). The comments name two programs of ours that are not
  part of this folder (an enumerator and the DRAT-to-LRAT converter); the proof does not trust either.

What the proof trusts: the check of the LRAT certificate is evaluated with `native_decide`, so besides the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) it depends on the auxiliary axiom that `native_decide`
adds, which trusts Lean's compiler and runtime for that evaluation. There is no `sorry`. `test/Axioms.lean` prints the
axioms.

Build (Lean 4.33.1, formal-conjectures at 2f91d251c07fbbaf9435166d47c11e884a08a6cf, Mathlib as pinned in
`e982b/lake-manifest.json`; the Mathlib cache is a download of several gigabytes):

```sh
cd erdos982-n8/e982 && lake build
cd ../e982b && lake exe cache get && lake build
lake env lean test/Axioms.lean      # the axioms of erdos_982_eight and of the bridge
```

The lemmas, the encoding and the Lean proof were written by an AI agent (Claude, Anthropic) working for Quantavane,
and checked independently: a second encoding of the lemmas, written separately, is unsatisfiable in three other SAT
solvers, with controls that are satisfiable where they should be. Arhan Canli takes responsibility for the result.

## Erdős Problem #982 for every n up to 13 (`erdos982-le13/`)

The same question for every n with 3 <= n <= 13, in formal-conjectures' form:

```lean
theorem E982C.erdos_982_le_thirteen (n : ℕ) (hn : 3 ≤ n) (h13 : n ≤ 13) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : Function.Injective p) (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2
```

(`test/Statement12.lean` checks with `type_of%` that this is formal-conjectures' `Erdos982.erdos_982 n hn`.) Before
this, the published general bounds settled only n <= 7 and n = 9. As for n = 8, Lean itself writes each case as a
CNF from geometric lemmas proved in Lean, and Lean's verified LRAT checker checks a SAT solver's refutation. The case
n = 12 needs one more geometric fact: five particular equal distances in a convex 12-gon would force its angles to
add up to 45 degrees more than they can; Lean proves this from a weighted sum of 71 angle equations (triangle sums,
angle additivity at a vertex, isosceles base angles), for all 24 symmetric images at once. With those 24 clauses
added, CaDiCaL's refutation (2,505,174 lemmas after trimming) is checked inside Lean in ten chunks, whose joining
lemmas are proved for any clause lists. What the proof trusts is as for n = 8: the three standard axioms and the
`native_decide` axioms of the LRAT checks; no `sorry`. The proof data (4.1 GB) is not in this repository:
`erdos982-le13/lrat/make_12.sh` and `make_13.sh` regenerate it with CaDiCaL 3.0.1, and `lrat/n12.SHA256SUMS`
lets you check the result. Details, build order and memory needs: `erdos982-le13/README.md`.

## Licence

Apache License 2.0 (see `LICENSE`), the licence of formal-conjectures and Mathlib.

## How to cite

```bibtex
@misc{quantavane-lean,
  author       = {Canli, Arhan},
  title        = {Lean proofs from Quantavane: Erd{\H{o}}s Problem \#982 for every n up to 13},
  year         = {2026},
  howpublished = {\url{https://github.com/arhancanli/quantavane-lean}},
  note         = {Quantavane; Apache License 2.0}
}
```

Cite Erdős Problem #982 at erdosproblems.com and the formal-conjectures statement as well.

Arhan Canli, Quantavane · quantavane.com

Known uses of this work are listed in [USED_BY.md](USED_BY.md). If you use it, please open an issue or a pull request
with a link so that yours can be added.
