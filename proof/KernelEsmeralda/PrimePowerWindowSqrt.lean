import KernelEsmeralda.PrimePowerWindow

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

theorem upperSquare_rpow_half (n : Nat) :
    upperSquare n ^ (1 / (2 : Real)) = (((n + 1 : Nat) : Real)) := by
  rw [← Real.sqrt_eq_rpow, upperSquare]
  simpa using Real.sqrt_sq (show 0 ≤ (((n + 1 : Nat) : Real)) by positivity)

theorem lowerSquare_rpow_half (n : Nat) :
    lowerSquare n ^ (1 / (2 : Real)) = (n : Real) := by
  rw [← Real.sqrt_eq_rpow, lowerSquare]
  simpa using Real.sqrt_sq (show 0 ≤ (n : Real) by positivity)

theorem psi_nat_succ_sub_eq_vonMangoldt (n : Nat) :
    Chebyshev.psi (((n + 1 : Nat) : Real)) - Chebyshev.psi (n : Real) =
      ArithmeticFunction.vonMangoldt (n + 1) := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  ring

theorem psi_nat_succ_sub_le_log (n : Nat) :
    Chebyshev.psi (((n + 1 : Nat) : Real)) - Chebyshev.psi (n : Real) ≤
      Real.log (((n + 1 : Nat) : Real)) := by
  rw [psi_nat_succ_sub_eq_vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_le_log

theorem remainderDelta_le_costa_window_sqrt (n : Nat) :
    higherPowerRemainder (upperSquare n) - higherPowerRemainder (lowerSquare n) <=
      (Chebyshev.psi (((n + 1 : Nat) : Real)) - Chebyshev.psi (n : Real)) +
      Chebyshev.psi (upperSquare n ^ (1 / (3 : Real))) +
      Chebyshev.psi (upperSquare n ^ (1 / (5 : Real))) := by
  rw [← upperSquare_rpow_half n, ← lowerSquare_rpow_half n]
  exact remainderDelta_le_costa_window n

theorem remainderDelta_le_log_add_roots (n : Nat) :
    higherPowerRemainder (upperSquare n) - higherPowerRemainder (lowerSquare n) <=
      Real.log (((n + 1 : Nat) : Real)) +
      Chebyshev.psi (upperSquare n ^ (1 / (3 : Real))) +
      Chebyshev.psi (upperSquare n ^ (1 / (5 : Real))) := by
  linarith [remainderDelta_le_costa_window_sqrt n, psi_nat_succ_sub_le_log n]

theorem remainderDelta_le_explicit_roots (n : Nat) :
    higherPowerRemainder (upperSquare n) - higherPowerRemainder (lowerSquare n) <=
      Real.log (((n + 1 : Nat) : Real)) +
      (Real.log 4 + 4) * (upperSquare n ^ (1 / (3 : Real))) +
      (Real.log 4 + 4) * (upperSquare n ^ (1 / (5 : Real))) := by
  have hu : 0 ≤ upperSquare n := by
    unfold upperSquare
    exact sq_nonneg _
  have h3 := Chebyshev.psi_le_const_mul_self
    (x := upperSquare n ^ (1 / (3 : Real))) (Real.rpow_nonneg hu _)
  have h5 := Chebyshev.psi_le_const_mul_self
    (x := upperSquare n ^ (1 / (5 : Real))) (Real.rpow_nonneg hu _)
  linarith [remainderDelta_le_log_add_roots n, h3, h5]

end
end KernelEsmeralda
