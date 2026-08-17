import KernelEsmeralda.ImaginaryCompressionBound
import KernelEsmeralda.GammaOfGeometry

namespace KernelEsmeralda

noncomputable section

/-- At the natural Zeta23 margin `D₀ = √T`, an interior zeta zero has an
explicit compression-loss bound.  This theorem keeps the Fourier decay
envelope untouched; a separate strip lemma bounds that envelope uniformly. -/
theorem zetaZero_imaginaryCompressionLoss_le_D0
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 0 < T)
    (hhD : P.hgrid T < Zeta23.D0 T)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T) :
    imaginaryCompressionLoss P T (Zeta23.gammaOf (rho : Complex)) ≤
      2 * (imaginaryEnergyDecayEnvelope P T
        (Zeta23.gammaOf (rho : Complex))) ^ 2 *
        ((((Zeta23.D0 T) + P.hgrid T) ^ 4)⁻¹ +
          (((Zeta23.D0 T) + P.hgrid T) ^ 3)⁻¹ /
            (3 * P.hgrid T)) +
      2 * (imaginaryEnergyDecayEnvelope P T
        (Zeta23.gammaOf (rho : Complex))) ^ 2 *
        ((((Zeta23.D0 T) - P.hgrid T) ^ 4)⁻¹ +
          (((Zeta23.D0 T) - P.hgrid T) ^ 3)⁻¹ /
            (3 * P.hgrid T)) := by
  have hD : 0 < Zeta23.D0 T := by
    unfold Zeta23.D0
    exact Real.sqrt_pos.2 hT
  have hzL :
      T + Zeta23.D0 T ≤ (Zeta23.gammaOf (rho : Complex)).re := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordL
  have hzR :
      (Zeta23.gammaOf (rho : Complex)).re ≤ 2 * T - Zeta23.D0 T := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordR
  exact imaginaryCompressionLoss_le_interior
    P T (Zeta23.D0 T) hP hwL (Zeta23.gammaOf (rho : Complex))
    hD hhD hzL hzR

/-- The corresponding finite matrix energy retains the full imaginary Poisson
energy up to the same explicit square-root-margin tail. -/
theorem zetaZero_finiteImaginaryEnergy_ge_full_sub_D0_tail
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 0 < T)
    (hhD : P.hgrid T < Zeta23.D0 T)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T) :
    fullImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
      (2 * (imaginaryEnergyDecayEnvelope P T
        (Zeta23.gammaOf (rho : Complex))) ^ 2 *
        ((((Zeta23.D0 T) + P.hgrid T) ^ 4)⁻¹ +
          (((Zeta23.D0 T) + P.hgrid T) ^ 3)⁻¹ /
            (3 * P.hgrid T)) +
       2 * (imaginaryEnergyDecayEnvelope P T
        (Zeta23.gammaOf (rho : Complex))) ^ 2 *
        ((((Zeta23.D0 T) - P.hgrid T) ^ 4)⁻¹ +
          (((Zeta23.D0 T) - P.hgrid T) ^ 3)⁻¹ /
            (3 * P.hgrid T))) ≤
      finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
  have hD : 0 < Zeta23.D0 T := by
    unfold Zeta23.D0
    exact Real.sqrt_pos.2 hT
  have hzL :
      T + Zeta23.D0 T ≤ (Zeta23.gammaOf (rho : Complex)).re := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordL
  have hzR :
      (Zeta23.gammaOf (rho : Complex)).re ≤ 2 * T - Zeta23.D0 T := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordR
  exact finiteImaginaryEnergy_ge_full_sub_interior_tail
    P T (Zeta23.D0 T) hP hwL (Zeta23.gammaOf (rho : Complex))
    hD hhD hzL hzR

end
end KernelEsmeralda
