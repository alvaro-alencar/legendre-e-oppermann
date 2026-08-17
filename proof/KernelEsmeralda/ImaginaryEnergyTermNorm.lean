import KernelEsmeralda.ImaginaryCompressionTail

namespace KernelEsmeralda

noncomputable section

/-- The imaginary-energy summand is bounded by twice the squared complex norm
of the same Fourier sample. -/
theorem imaginaryEnergyTerm_le_two_norm_sq
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : ℤ) :
    imaginaryEnergyTerm P T z k ≤
      2 * ‖P.phiHat T (z - (P.tau T k : ℂ))‖ ^ 2 := by
  unfold imaginaryEnergyTerm
  have him := Complex.abs_im_le_norm
    (P.phiHat T (z - (P.tau T k : ℂ)))
  have hs := pow_le_pow_left₀
    (abs_nonneg (P.phiHat T (z - (P.tau T k : ℂ))).im) him 2
  rw [sq_abs] at hs
  nlinarith

end
end KernelEsmeralda