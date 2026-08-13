import KernelEsmeralda.PoleAnalysis

namespace KernelEsmeralda

noncomputable section

theorem emeraldPaperFT_pos_pole (K : Real → Real) :
    emeraldPaperFT K (Complex.I / 2) = ∫ u : Real, (K u : Complex) := by
  unfold emeraldPaperFT
  simp_rw [emeraldPolePos_integrand]

theorem emeraldPaperFT_neg_pole (K : Real → Real) :
    emeraldPaperFT K (-Complex.I / 2) =
      ∫ u : Real, ((Real.exp u * K u : Real) : Complex) := by
  unfold emeraldPaperFT
  simp_rw [emeraldPoleNeg_integrand]

end
end KernelEsmeralda
