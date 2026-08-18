import KernelEsmeralda.DeepRetainedPairCorrelations

namespace KernelEsmeralda

noncomputable section

/-- The hyperbolic quadratic combination of the four resolved correlations
associated with two complex kernels. -/
def hyperbolicResolvedKernelInteraction (K Kc : ℂ) : ℝ :=
  (K.re + Kc.re) ^ 2 +
    (Kc.re - K.re) ^ 2 -
    (K.im - Kc.im) ^ 2 -
    (K.im + Kc.im) ^ 2

/-- The four real resolved correlations collapse to twice the real part of the
sum of two complex squares. -/
theorem hyperbolicResolvedKernelInteraction_eq_two_re_sq_add
    (K Kc : ℂ) :
    hyperbolicResolvedKernelInteraction K Kc =
      2 * (K ^ 2 + Kc ^ 2).re := by
  unfold hyperbolicResolvedKernelInteraction
  simp [pow_two, Complex.mul_re]
  ring

/-- Specialized to the zeta Poisson kernels, the ideal cross-pair interaction
is `2 L² Re(Phi(γρ-γσ)² + Phi(γρ-conj γσ)²)`. -/
theorem zeta_hyperbolicResolvedKernelInteraction
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    hyperbolicResolvedKernelInteraction
        (zetaFiniteCorrelationKernel P T rho sigma)
        (zetaFiniteConjCorrelationKernel P T rho sigma) =
      2 * (P.L T) ^ 2 *
        (P.Phi T
            (Zeta23.gammaOf (rho : Complex) -
              Zeta23.gammaOf (sigma : Complex)) ^ 2 +
          P.Phi T
            (Zeta23.gammaOf (rho : Complex) -
              starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))) ^ 2).re := by
  rw [hyperbolicResolvedKernelInteraction_eq_two_re_sq_add]
  unfold zetaFiniteCorrelationKernel zetaFiniteConjCorrelationKernel
  push_cast
  simp only [mul_pow]
  have hL : ((P.L T : ℂ) ^ 2) = (((P.L T) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hL]
  simp [Complex.add_re, Complex.mul_re]
  ring

end
end KernelEsmeralda
