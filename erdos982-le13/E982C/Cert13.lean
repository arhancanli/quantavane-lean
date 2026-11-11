/-
Erdős #982, round 2: `gen 13 5` is unsatisfiable. LRAT certificate: CaDiCaL 2.1.2 (`--lrat=true --binary=false`),
trimmed to the 391,166 lemmas reachable from the empty clause and renumbered consecutively
(`lrat/make_13.sh` regenerates it and checks SHA-256 1fcedc5b...; the file is 234 MB and is not in git), checked by
Lean's verified LRAT checker evaluated by `native_decide`.
-/
import E982C.Cnf

open Std.Sat Std.Tactic.BVDecide

namespace E982C

/-- Std-only module (no Mathlib import), to keep the native evaluation small. -/
def proof13 : Array LRAT.IntAction :=
  match LRAT.parseLRATProof (include_str "../lrat/gen_13_5.lrat").toUTF8 with
  | .ok p => p
  | .error _ => #[]

theorem gen_13_unsat : (gen 13 5).Unsat := LRAT.check_sound proof13 (gen 13 5) (by native_decide)

end E982C
