import KernelEsmeralda.FiniteSquareGeometry

namespace KernelEsmeralda

noncomputable section

/-- Scalar core of the deep-pair Frobenius estimate.  If the doubled real and
imaginary energies satisfy `Er ≥ L²`, `Ei ≥ L²/2`, while the doubled cross
energy has `|Ec| ≤ L²/4`, then the hyperbolic quadratic combination pays at
least `9/8 L⁴`. -/
theorem hyperbolic_energy_cost_ge_nine_eighths
    {L Er Ei Ec : ℝ}
    (hEr : L ^ 2 ≤ Er)
    (hEi : L ^ 2 / 2 ≤ Ei)
    (hEc : |Ec| ≤ L ^ 2 / 4) :
    9 / 8 * L ^ 4 ≤ Er ^ 2 + Ei ^ 2 - 2 * Ec ^ 2 := by
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hEr0 : 0 ≤ Er := hL2.trans hEr
  have hEi0 : 0 ≤ Ei := by linarith
  have hErSq : (L ^ 2) ^ 2 ≤ Er ^ 2 := by
    have hdiff : 0 ≤ Er - L ^ 2 := sub_nonneg.mpr hEr
    have hsum : 0 ≤ Er + L ^ 2 := add_nonneg hEr0 hL2
    nlinarith [mul_nonneg hdiff hsum]
  have hEiSq : (L ^ 2 / 2) ^ 2 ≤ Ei ^ 2 := by
    have hbase0 : 0 ≤ L ^ 2 / 2 := by positivity
    have hdiff : 0 ≤ Ei - L ^ 2 / 2 := sub_nonneg.mpr hEi
    have hsum : 0 ≤ Ei + L ^ 2 / 2 := add_nonneg hEi0 hbase0
    nlinarith [mul_nonneg hdiff hsum]
  have hEcBounds := abs_le.mp hEc
  have hEcSq : Ec ^ 2 ≤ (L ^ 2 / 4) ^ 2 := by
    have hB : 0 ≤ L ^ 2 / 4 := by positivity
    have hleft : 0 ≤ Ec + L ^ 2 / 4 := by linarith [hEcBounds.1]
    have hright : 0 ≤ L ^ 2 / 4 - Ec := by linarith [hEcBounds.2]
    nlinarith [mul_nonneg hleft hright]
  nlinarith [hErSq, hEiSq, hEcSq]

end
end KernelEsmeralda
