/-
The CNF `E982B.gen` (= `genA` relabelled to `Nat`) is unsatisfiable: an LRAT certificate (CaDiCaL 1.5.3 DRAT,
converted by engine/drat2lrat.py; SHA-256 e5b4ae7f...e85d0c9) checked by Lean's verified LRAT checker. The check is
evaluated by `native_decide`, so `gen_unsat` depends on the auxiliary axiom that `native_decide` adds (trust in Lean's
compiler and runtime) besides the standard axioms. `genA_unsat` transfers the result to assignments of the atoms.
-/
import E982B.Cnf

open Std.Sat Std.Tactic.BVDecide

namespace E982B

def proofB : Array LRAT.IntAction :=
  match LRAT.parseLRATProof (include_str "../lrat/genB.lrat").toUTF8 with
  | .ok p => p
  | .error _ => #[]

theorem gen_unsat : gen.Unsat := LRAT.check_sound proofB gen (by native_decide)

theorem genA_unsat (a : Atom → Bool) : genA.eval a = false := by
  have h := gen_unsat (fun x => a (dec x))
  unfold gen at h
  rw [CNF.eval_relabel] at h
  have hc : ((fun x => a (dec x)) ∘ enc) = a := by
    funext x
    simp [dec_enc]
  rw [hc] at h
  exact h

end E982B
