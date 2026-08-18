import KernelEsmeralda.PoleReal

namespace KernelEsmeralda

noncomputable section

theorem emeraldPaperFT_pos_pole_re_nonneg
    (K : Real → Real) (hKnonneg : ∀ u : Real, 0 ≤ K u) :
    0 ≤ (emeraldPaperFT K (Complex.I / 2)).re := by
  rw [emeraldPaperFT_pos_pole_re]
  apply MeasureTheory.integral_nonneg
  exact hKnonneg

end
end KernelEsmeralda
