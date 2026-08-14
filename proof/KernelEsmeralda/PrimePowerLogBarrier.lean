import KernelEsmeralda.PrimePowerExponentBound

open Finset

namespace KernelEsmeralda

noncomputable section

def primePowerCountBarrier (n : Nat) : Real :=
  (higherPowerExponentCutoff n : Real) * Real.log (upperSquare n)

def primePowerLogBarrier (n : Nat) : Real :=
  (Real.log (upperSquare n)) ^ 2 / Real.log 2

theorem higherPowerRemainderDelta_le_countBarrier
    (n : Nat) (hn : 2 ≤ n) :
    higherPowerRemainder (upperSquare n) -
        higherPowerRemainder (lowerSquare n) ≤
      primePowerCountBarrier n := by
  rw [higherPowerRemainderDelta_eq_exponent_sum n hn]
  have hnr : (2 : Real) ≤ n := by exact_mod_cast hn
  have hu1 : (1 : Real) ≤ upperSquare n := by
    unfold upperSquare
    nlinarith [sq_nonneg (((n + 1 : Nat) : Real) - 1)]
  have hlog0 : 0 ≤ Real.log (upperSquare n) := Real.log_nonneg hu1
  calc
    (∑ k ∈ Icc 2 (higherPowerExponentCutoff n),
        (Chebyshev.theta (upperSquare n ^ ((1 : Real) / k)) -
          Chebyshev.theta (lowerSquare n ^ ((1 : Real) / k))))
        ≤ ∑ k ∈ Icc 2 (higherPowerExponentCutoff n),
            Real.log (upperSquare n) := by
          apply sum_le_sum
          intro k hkset
          exact primePowerExponent_thetaDiff_le_log_upper n k hn
            (mem_Icc.mp hkset).1
    _ = ((Icc 2 (higherPowerExponentCutoff n)).card : Real) *
          Real.log (upperSquare n) := by simp
    _ ≤ (higherPowerExponentCutoff n : Real) * Real.log (upperSquare n) := by
          apply mul_le_mul_of_nonneg_right _ hlog0
          exact_mod_cast (show (Icc 2 (higherPowerExponentCutoff n)).card ≤
            higherPowerExponentCutoff n by simp; omega)
    _ = primePowerCountBarrier n := rfl

theorem higherPowerExponentCutoff_le_log_ratio
    (n : Nat) (hn : 2 ≤ n) :
    (higherPowerExponentCutoff n : Real) ≤
      Real.log (upperSquare n) / Real.log 2 := by
  have hnr : (2 : Real) ≤ n := by exact_mod_cast hn
  have hu1 : (1 : Real) ≤ upperSquare n := by
    unfold upperSquare
    nlinarith [sq_nonneg (((n + 1 : Nat) : Real) - 1)]
  have hlog0 : 0 ≤ Real.log (upperSquare n) := Real.log_nonneg hu1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold higherPowerExponentCutoff
  exact Nat.floor_le (div_nonneg hlog0 hlog2.le)

theorem higherPowerRemainderDelta_le_logBarrier
    (n : Nat) (hn : 2 ≤ n) :
    higherPowerRemainder (upperSquare n) -
        higherPowerRemainder (lowerSquare n) ≤
      primePowerLogBarrier n := by
  have hcount := higherPowerRemainderDelta_le_countBarrier n hn
  have hN := higherPowerExponentCutoff_le_log_ratio n hn
  have hnr : (2 : Real) ≤ n := by exact_mod_cast hn
  have hu1 : (1 : Real) ≤ upperSquare n := by
    unfold upperSquare
    nlinarith [sq_nonneg (((n + 1 : Nat) : Real) - 1)]
  have hlog0 : 0 ≤ Real.log (upperSquare n) := Real.log_nonneg hu1
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : Real) < 2)).ne'
  apply hcount.trans
  unfold primePowerCountBarrier primePowerLogBarrier
  have hmul := mul_le_mul_of_nonneg_right hN hlog0
  calc
    (higherPowerExponentCutoff n : Real) * Real.log (upperSquare n)
        ≤ (Real.log (upperSquare n) / Real.log 2) *
            Real.log (upperSquare n) := hmul
    _ = (Real.log (upperSquare n)) ^ 2 / Real.log 2 := by
      field_simp [hlog2]
      ring

end
end KernelEsmeralda
