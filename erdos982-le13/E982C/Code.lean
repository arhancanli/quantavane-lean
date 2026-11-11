/-
Erdős #982, round 2: the code `enc` of the atoms is injective (`dec_enc`).
-/
import E982C.Cnf
import Mathlib.Tactic

namespace E982C

variable {n : Nat} [NeZero n]

theorem fm_val (a : Fin n) : fm (n := n) a.val = a := by
  apply Fin.ext; simp [fm, Nat.mod_eq_of_lt a.isLt]

theorem code_lt (P : Fin n × Fin n) : code P < n * n := by
  unfold code
  have h1 := P.1.isLt
  have h2 := P.2.isLt
  calc P.1.val * n + P.2.val < P.1.val * n + n := by omega
    _ = (P.1.val + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ h1

theorem decP_code (P : Fin n × Fin n) : decP (code P) = P := by
  have hn := n_pos (n := n)
  have h2 := P.2.isLt
  have hd : (P.1.val * n + P.2.val) / n = P.1.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt h2, Nat.zero_add]
  have hm : (P.1.val * n + P.2.val) % n = P.2.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  unfold decP code
  rw [hd]
  ext
  · simp [fm, Nat.mod_eq_of_lt P.1.isLt]
  · simp [fm, hm]

theorem div_nn (P Q : Fin n × Fin n) : (code P * (n * n) + code Q) / (n * n) = code P := by
  have hq := code_lt Q
  have hnn : 0 < n * n := Nat.mul_pos n_pos n_pos
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnn, Nat.div_eq_of_lt hq, Nat.zero_add]

theorem mod_nn (P Q : Fin n × Fin n) : (code P * (n * n) + code Q) % (n * n) = code Q := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (code_lt Q)]

theorem pq_lt (P Q : Fin n × Fin n) : code P * (n * n) + code Q < n * n * (n * n) := by
  have hp := code_lt P
  have hq := code_lt Q
  calc code P * (n * n) + code Q < code P * (n * n) + n * n := by omega
    _ = (code P + 1) * (n * n) := by ring
    _ ≤ n * n * (n * n) := Nat.mul_le_mul_right _ hp

theorem dec_enc (x : Atom n) : dec (enc x) = x := by
  rcases x with ⟨P, Q⟩ | ⟨P, Q⟩ | v
  · have h := pq_lt P Q
    simp only [enc, dec, if_pos h, div_nn, mod_nn, decP_code]
  · have h := pq_lt P Q
    have h1 : ¬ (n * n * (n * n) + (code P * (n * n) + code Q) < n * n * (n * n)) := by omega
    have h2 : n * n * (n * n) + (code P * (n * n) + code Q) < 2 * (n * n * (n * n)) := by omega
    have h3 : n * n * (n * n) + (code P * (n * n) + code Q) - n * n * (n * n) = code P * (n * n) + code Q := by
      omega
    simp only [enc, dec, if_neg h1, if_pos h2, h3, div_nn, mod_nn, decP_code]
  · have h1 : ¬ (2 * (n * n * (n * n)) + v.val < n * n * (n * n)) := by omega
    have h2 : ¬ (2 * (n * n * (n * n)) + v.val < 2 * (n * n * (n * n))) := by omega
    have h3 : 2 * (n * n * (n * n)) + v.val - 2 * (n * n * (n * n)) = v.val := by omega
    simp only [enc, dec, if_neg h1, if_neg h2, h3, fm_val]

end E982C
