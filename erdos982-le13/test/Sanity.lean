import E982C.Cert
open Std.Sat Std.Tactic.BVDecide
namespace E982C
/-- the certificate parsed (one action per LRAT line) -/
example : proof10.size = 20096 := by native_decide
/-- red control: the n = 10 certificate does not refute `gen 10 5` (regular decagon: 5 distances per vertex) -/
example : LRAT.check proof10 (gen 10 5) = false := by native_decide
/-- red control: without its last step it refutes nothing -/
example : LRAT.check proof10.pop (gen 10 4) = false := by native_decide
/-- red control: the n = 8 certificate does not refute `gen 8 4` -/
example : LRAT.check proof8 (gen 8 4) = false := by native_decide
end E982C
