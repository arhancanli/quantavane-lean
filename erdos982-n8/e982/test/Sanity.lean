import E982.Lrat
open Std.Sat Std.Tactic.BVDecide
#eval E982.proof83.size
#eval (E982.gen 8 3).clauses.size
#eval LRAT.check E982.proof83 (E982.gen 8 3)
#eval LRAT.check E982.proof83 (E982.gen 8 4)
#eval LRAT.check (E982.proof83.pop) (E982.gen 8 3)
#print axioms E982.gen_8_3_unsat
