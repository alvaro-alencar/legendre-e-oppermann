import KernelEsmeralda.PrimePowerWindow

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

theorem remainderDelta_le_costa_window_sqrt (n : Nat) :
    higherPowerRemainder (upperSquare n) - higherPowerRemainder (lowerSquare n) <=
      (Chebyshev.psi (((n + 1 : Nat) : Real)) - Chebyshev.psi (n : Real)) +
      Chebyshev.psi (upperSquare n ^ (1 / (3 : Real))) +
      Chebyshev.psi (upperSquare n ^ (1 / (5 : Real))) := by
  rw [← upperSquare_rpow_half n, ← lowerSquare_rpow_half n]
  exact remainderDelta_le_costa_window n

end
end KernelEsmeralda
