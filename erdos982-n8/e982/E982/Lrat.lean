/-
Erdős Problem #982, case n = 8, combinatorial core: the CNF `E982.gen 8 3` (see E982/Gen.lean) is unsatisfiable.

The certificate is an LRAT proof (CaDiCaL 1.5.3 via pysat, DRAT converted to LRAT by engine/drat2lrat.py) checked by
Lean's verified LRAT checker `Std.Tactic.BVDecide.LRAT.check` with its soundness theorem `check_sound`. The check is
evaluated with `native_decide`, so the theorem depends on the axiom `Lean.ofReduceBool` (trust in Lean's compiler
and runtime), besides the standard axioms.
-/
import E982.Gen
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

namespace E982

/-- The LRAT certificate for `gen 8 3`. -/
def proof83 : Array LRAT.IntAction :=
  match LRAT.parseLRATProof (include_str "../lrat/gen_8_3.lrat").toUTF8 with
  | .ok p => p
  | .error _ => #[]

theorem gen_8_3_unsat : (gen 8 3).Unsat :=
  LRAT.check_sound proof83 (gen 8 3) (by native_decide)

end E982
