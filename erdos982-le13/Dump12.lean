import E982C.Cnf12

/-- `dump12 path`: write `E982C.gen12` (gen 12 5 plus the 24 cut clauses) in DIMACS. -/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let g := E982C.gen12
    IO.FS.writeFile path g.dimacs
    IO.println s!"wrote {g.clauses.size} clauses to {path}"
  | _ => IO.eprintln "usage: dump12 path"
