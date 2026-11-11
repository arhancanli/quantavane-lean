import E982C.Cnf

/-- `dumpc n K path`: write `E982C.gen n K` in DIMACS (atom code i becomes variable i + 1). -/
def main (args : List String) : IO Unit := do
  match args with
  | [ns, ks, path] =>
    let n := ns.toNat!
    let K := ks.toNat!
    if h : n = 0 then IO.eprintln "n must be positive" else
    have : NeZero n := ⟨h⟩
    let g := E982C.gen n K
    IO.FS.writeFile path g.dimacs
    IO.println s!"wrote {g.clauses.size} clauses to {path}"
  | _ => IO.eprintln "usage: dumpc n K path"
