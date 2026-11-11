/-
Erdős #982, round 2: the CNFs `gen n K` for (n, K) = (4, 1), (6, 2), (8, 3), (10, 4) are unsatisfiable. Each is
refuted by an LRAT certificate (CaDiCaL 2.1.2, the solver shipped with Lean 4.33.1, `--lrat=true --binary=false`)
checked by Lean's verified LRAT checker `Std.Tactic.BVDecide.LRAT.check`. The check is evaluated by `native_decide`,
so these theorems depend on the auxiliary axiom `native_decide` adds (trust in Lean's compiler and runtime) besides
the standard axioms.
-/
import E982C.Bridge

open Std.Sat Std.Tactic.BVDecide

namespace E982C

def parseProof (s : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]

def proof4 : Array LRAT.IntAction := parseProof (include_str "../lrat/gen_4_1.lrat")
def proof6 : Array LRAT.IntAction := parseProof (include_str "../lrat/gen_6_2.lrat")
def proof8 : Array LRAT.IntAction := parseProof (include_str "../lrat/gen_8_3.lrat")
def proof10 : Array LRAT.IntAction := parseProof (include_str "../lrat/gen_10_4.lrat")

theorem gen_4_unsat : (gen 4 1).Unsat := LRAT.check_sound proof4 (gen 4 1) (by native_decide)
theorem gen_6_unsat : (gen 6 2).Unsat := LRAT.check_sound proof6 (gen 6 2) (by native_decide)
theorem gen_8_unsat : (gen 8 3).Unsat := LRAT.check_sound proof8 (gen 8 3) (by native_decide)
theorem gen_10_unsat : (gen 10 4).Unsat := LRAT.check_sound proof10 (gen 10 4) (by native_decide)

end E982C
