import KernelEsmeralda.ImaginaryCompressionBound
import KernelEsmeralda.GammaOfGeometry

namespace KernelEsmeralda

noncomputable section

/-- The second-derivative taper constant is nonnegative. -/
theorem zeta23_params_C1_nonneg
    (P : Zeta23.Params) (T : ℝ) :
    0 ≤ P.C1 T := by
  unfold Zeta23.Params.C1 Zeta23.Taper.C1
  exact MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)

/-- On every nontrivial zeta zero, the strip geometry bounds the exponential
part of the complex Fourier decay envelope by `exp(L/4)`. -/
theorem zetaZero_imaginaryEnergyDecayEnvelope_le
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    imaginaryEnergyDecayEnvelope P T (Zeta23.gammaOf (rho : Complex)) ≤
      Real.exp (P.L T / 4) * (P.L T + P.C1 T) := by
  have hL : 0 ≤ P.L T := by
    linarith [hP.one_le_w]
  have hC1 : 0 ≤ P.C1 T := zeta23_params_C1_nonneg P T
  have hLC : 0 ≤ P.L T + P.C1 T := add_nonneg hL hC1
  have him := zetaZero_abs_gammaOf_im_le_half rho
  have hhalfL : 0 ≤ P.L T / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right him hhalfL
  have harg :
      |(Zeta23.gammaOf (rho : Complex)).im| * (P.L T / 2) ≤
        P.L T / 4 := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr harg
  unfold imaginaryEnergyDecayEnvelope
  exact mul_le_mul_of_nonneg_right hexp hLC

end
end KernelEsmeralda
