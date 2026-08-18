import KernelEsmeralda.DeepPairKernelInterference

namespace KernelEsmeralda

noncomputable section

/-- The ideal imaginary-ray interaction is a single complex-square real part. -/
theorem idealImagRayInteraction_eq_neg_re_square
    (K Kc : ℂ) :
    (K.im + Kc.im) ^ 2 - (Kc.re - K.re) ^ 2 =
      -(Kc - starRingEnd ℂ K) ^ 2 |>.re := by
  simp [pow_two, Complex.mul_re]
  ring

/-- Kernel form for zeta pairs. -/
theorem zetaIdealImagRayInteraction_eq_neg_re_square
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    zetaIdealImagRayInteraction P T rho sigma =
      -((zetaFiniteConjCorrelationKernel P T rho sigma -
          starRingEnd ℂ (zetaFiniteCorrelationKernel P T rho sigma)) ^ 2).re := by
  unfold zetaIdealImagRayInteraction
  exact idealImagRayInteraction_eq_neg_re_square _ _

/-- Pulling out the real scale `L` leaves a dimensionless Phi-kernel square. -/
theorem zetaIdealImagRayInteraction_eq_neg_L_sq_re_phi_square
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    zetaIdealImagRayInteraction P T rho sigma =
      -(P.L T) ^ 2 *
        ((P.Phi T
              (Zeta23.gammaOf (rho : Complex) -
                starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))) -
            starRingEnd ℂ
              (P.Phi T
                (Zeta23.gammaOf (rho : Complex) -
                  Zeta23.gammaOf (sigma : Complex)))) ^ 2).re := by
  rw [zetaIdealImagRayInteraction_eq_neg_re_square]
  unfold zetaFiniteConjCorrelationKernel zetaFiniteCorrelationKernel
  have hstarL : starRingEnd ℂ (P.L T : ℂ) = (P.L T : ℂ) := by simp
  rw [map_mul, hstarL]
  have hfactor :
      (P.L T : ℂ) *
          P.Phi T
            (Zeta23.gammaOf (rho : Complex) -
              starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))) -
        (P.L T : ℂ) *
          starRingEnd ℂ
            (P.Phi T
              (Zeta23.gammaOf (rho : Complex) -
                Zeta23.gammaOf (sigma : Complex))) =
      (P.L T : ℂ) *
        (P.Phi T
            (Zeta23.gammaOf (rho : Complex) -
              starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))) -
          starRingEnd ℂ
            (P.Phi T
              (Zeta23.gammaOf (rho : Complex) -
                Zeta23.gammaOf (sigma : Complex)))) := by ring
  rw [hfactor, mul_pow]
  have hL2 : ((P.L T : ℂ) ^ 2) = (((P.L T) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hL2]
  simp [Complex.mul_re]
  ring

end
end KernelEsmeralda
