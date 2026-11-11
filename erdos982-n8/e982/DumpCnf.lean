import E982.Gen

/-- `dumpcnf n K path`: write the CNF `E982.gen n K` in DIMACS (atom i becomes variable i + 1). -/
def main (args : List String) : IO Unit := do
  match args with
  | [n, k, path] =>
    let f := E982.gen n.toNat! k.toNat!
    IO.FS.writeFile path f.dimacs
    IO.println s!"wrote {f.clauses.size} clauses to {path}"
  | _ => IO.eprintln "usage: dumpcnf n K path"
