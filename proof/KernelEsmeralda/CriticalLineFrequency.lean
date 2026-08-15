import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import KernelEsmeralda.EmeraldTaper

namespace KernelEsmeralda

noncomputable section

theorem emeraldTaperCenter_eq_log_add_log
    (n : Nat) (hn : 1 ≤ n) :
    emeraldTaperCenter n =
      Real.log (n : Real) + Real.log (((n + 1 : Nat) : Real)) := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  unfold emeraldTaperCenter emeraldLogLeft emeraldLogRight lowerSquare upperSquare
  rw [show (n : Real) ^ 2 = (n : Real) * (n : Real) by ring]
  rw [show (((n + 1 : Nat) : Real)) ^ 2 =
      (((n + 1 : Nat) : Real)) * (((n + 1 : Nat) : Real)) by ring]
  rw [Real.log_mul hnpos.ne' hnpos.ne', Real.log_mul hspos.ne' hspos.ne']
  ring

theorem two_log_n_lt_emeraldTaperCenter
    (n : Nat) (hn : 1 ≤ n) :
    2 * Real.log (n : Real) < emeraldTaperCenter n := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsucc : (n : Real) < (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.lt_succ_self n
  have hlog : Real.log (n : Real) < Real.log (((n + 1 : Nat) : Real)) :=
    Real.strictMonoOn_log hsucc
  rw [emeraldTaperCenter_eq_log_add_log n hn]
  linarith

/-- At the natural difficult zero height T=n, the translated Emerald test has
normalized logarithmic frequency strictly larger than 2. -/
theorem two_lt_emeraldNaturalFrequency
    (n : Nat) (hn : 2 ≤ n) :
    2 < emeraldTaperCenter n / Real.log (n : Real) := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnR : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : Real) := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : Real) < 2) hnR)
  have hcenter := two_log_n_lt_emeraldTaperCenter n hn1
  rw [lt_div_iff₀ hlogpos]
  simpa [mul_comm] using hcenter

end
end KernelEsmeralda
