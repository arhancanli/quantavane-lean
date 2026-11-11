import E982B.Cnf

/-- `dumpb path`: write `E982B.gen` in DIMACS (atom i becomes variable i + 1). -/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    IO.FS.writeFile path E982B.gen.dimacs
    IO.println s!"wrote {E982B.gen.clauses.size} clauses to {path}"
  | _ => IO.eprintln "usage: dumpb path"
