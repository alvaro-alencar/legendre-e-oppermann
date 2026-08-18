import KernelEsmeralda.OffLineComplexEnergy
import KernelEsmeralda.FiniteImaginaryEnergy

namespace KernelEsmeralda

noncomputable section

/-- Quantitative finite-compression lower bound for a left-half zeta zero.
All difficult leakage is isolated in the single hypothesis `hloss`. -/
theorem zeta_zero_left_half_finite_energy_lower
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hre : (rho : ℂ).re ≤ 1 / 2)
    {R : ℝ}
    (hloss :
      imaginaryCompressionLoss P T (Zeta23.gammaOf (rho : ℂ)) ≤ R) :
    P.L T *
          ((P.w / 2) *
            Real.exp
              ((1 - 2 * (rho : ℂ).re) *
                (P.L T / 2 - 3 * P.w / 2))) -
        P.a T * P.L T ^ 2 - R ≤
      finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : ℂ)) := by
  have hPhi := zeta_zero_left_half_complex_energy_lower P T hP hwL rho hre
  have hfull :
      P.L T *
            ((P.w / 2) *
              Real.exp
                ((1 - 2 * (rho : ℂ).re) *
                  (P.L T / 2 - 3 * P.w / 2))) -
          P.a T * P.L T ^ 2 ≤
        fullImaginaryEnergy P T (Zeta23.gammaOf (rho : ℂ)) := by
    unfold fullImaginaryEnergy
    linarith
  have hfinite :=
    finiteImaginaryEnergy_ge_full_sub_lossBound
      P T (Zeta23.gammaOf (rho : ℂ)) hloss
  linarith

end
end KernelEsmeralda