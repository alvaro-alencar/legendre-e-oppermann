import KernelEsmeralda.ChebyshevBridge

namespace KernelEsmeralda

noncomputable section

theorem remainderDelta_le_costa_window (n : Nat) :
    higherPowerRemainder (upperSquare n) - higherPowerRemainder (lowerSquare n) <=
      (Chebyshev.psi (upperSquare n ^ (1 / (2 : Real))) - Chebyshev.psi (lowerSquare n ^ (1 / (2 : Real)))) +
      Chebyshev.psi (upperSquare n ^ (1 / (3 : Real))) +
      Chebyshev.psi (upperSquare n ^ (1 / (5 : Real))) := by
  have hu := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (upperSquare n)
  have hl0 : 0 <= lowerSquare n := by simp [lowerSquare]
  have hl := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hl0
  have h3 : 0 <= Chebyshev.psi (lowerSquare n ^ (1 / (3 : Real))) := Chebyshev.psi_nonneg _
  have h7 : 0 <= Chebyshev.psi (lowerSquare n ^ (1 / (7 : Real))) := Chebyshev.psi_nonneg _
  norm_num only [one_div] at hu hl
  simp only [higherPowerRemainder] at hu hl ⊢
  linarith

end
end KernelEsmeralda
