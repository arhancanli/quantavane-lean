import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

/-!
`checklrat cnf lrat`: run Lean's verified LRAT checker (`Std.Tactic.BVDecide.LRAT.check`, sound by
`LRAT.check_sound`) on an external DIMACS file and an LRAT proof (text or binary). DIMACS variable v is atom v - 1,
as in `CNF.dimacs`. Only the DIMACS parser below is unverified.
-/

open Std.Sat Std.Tactic.BVDecide

def parseDimacs (s : String) : Except String (CNF Nat) := do
  let mut cls : Array (CNF.Clause Nat) := #[]
  let mut cur : CNF.Clause Nat := []
  for line in s.splitOn "\n" do
    let t := line.trim
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" then continue
    for tok in t.splitOn " " do
      if tok.isEmpty then continue
      match tok.toInt? with
      | none => throw s!"bad token {tok}"
      | some k =>
        if k == 0 then
          cls := cls.push cur.reverse
          cur := []
        else
          cur := (k.natAbs - 1, decide (k > 0)) :: cur
  if !cur.isEmpty then throw "unterminated clause"
  return ⟨cls⟩

def main (args : List String) : IO UInt32 := do
  match args with
  | [cnfPath, lratPath] =>
    let cnfStr ← IO.FS.readFile cnfPath
    match parseDimacs cnfStr with
    | .error e => IO.eprintln e; return 2
    | .ok cnf =>
      let bytes ← IO.FS.readBinFile lratPath
      match LRAT.parseLRATProof bytes with
      | .error e => IO.eprintln s!"proof parse error: {e}"; return 2
      | .ok proof =>
        IO.println s!"clauses {cnf.clauses.size}, proof steps {proof.size}"
        if LRAT.check proof cnf then
          IO.println "VERIFIED (empty clause derived)"
          return 0
        else
          IO.println "NOT VERIFIED"
          return 1
  | _ => IO.eprintln "usage: checklrat cnf lrat"; return 2
