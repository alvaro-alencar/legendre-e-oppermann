import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KernelEsmeralda.EmeraldTaper

namespace KernelEsmeralda

noncomputable section

theorem emeraldLeftMargin_ge_inv_four_n
    (n : Nat) (hn : 1 ≤ n) :
    1 / (4 * (n : Real)) ≤ emeraldLinearCoreLeft n - emeraldLogLeft n := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hleftpos : 0 < emeraldLinearCoreLeftX n := by
    unfold emeraldLinearCoreLeftX lowerSquare
    positivity
  have hratioPos : 0 < emeraldLinearCoreLeftX n / lowerSquare n :=
    div_pos hleftpos hlpos
  have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
  have hrat :
      1 / (4 * (n : Real)) ≤
        1 - (emeraldLinearCoreLeftX n / lowerSquare n)⁻¹ := by
    unfold emeraldLinearCoreLeftX lowerSquare
    push_cast
    field_simp [hnpos.ne']
    nlinarith
  have hmain :
      1 / (4 * (n : Real)) ≤
        Real.log (emeraldLinearCoreLeftX n / lowerSquare n) :=
    hrat.trans hlog
  unfold emeraldLinearCoreLeft emeraldLogLeft
  rw [Real.log_div hleftpos.ne' hlpos.ne'] at hmain
  exact hmain

theorem emeraldRightMargin_ge_inv_four_n
    (n : Nat) (hn : 1 ≤ n) :
    1 / (4 * (n : Real)) ≤ emeraldLogRight n - emeraldLinearCoreRight n := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hupperpos : 0 < upperSquare n := by
    unfold upperSquare
    positivity
  have hrightpos : 0 < emeraldLinearCoreRightX n := by
    unfold emeraldLinearCoreRightX lowerSquare
    positivity
  have hratioPos : 0 < upperSquare n / emeraldLinearCoreRightX n :=
    div_pos hupperpos hrightpos
  have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
  have hrat :
      1 / (4 * (n : Real)) ≤
        1 - (upperSquare n / emeraldLinearCoreRightX n)⁻¹ := by
    unfold upperSquare emeraldLinearCoreRightX lowerSquare
    push_cast
    field_simp [hnpos.ne']
    nlinarith
  have hmain :
      1 / (4 * (n : Real)) ≤
        Real.log (upperSquare n / emeraldLinearCoreRightX n) :=
    hrat.trans hlog
  unfold emeraldLogRight emeraldLinearCoreRight
  rw [Real.log_div hupperpos.ne' hrightpos.ne'] at hmain
  exact hmain

theorem emeraldTaperWidth_ge_inv_four_n
    (n : Nat) (hn : 1 ≤ n) :
    1 / (4 * (n : Real)) ≤ emeraldTaperWidth n := by
  unfold emeraldTaperWidth
  exact le_min (emeraldLeftMargin_ge_inv_four_n n hn)
    (emeraldRightMargin_ge_inv_four_n n hn)

end
end KernelEsmeralda
