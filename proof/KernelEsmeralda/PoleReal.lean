import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import KernelEsmeralda.PoleGlobalBound

namespace KernelEsmeralda

noncomputable section

theorem emeraldPaperFT_neg_pole_re (K : Real → Real) :
    (emeraldPaperFT K (-Complex.I / 2)).re =
      ∫ u : Real, Real.exp u * K u := by
  rw [emeraldPaperFT_neg_pole, integral_complex_ofReal]
  simp

end
end KernelEsmeralda
