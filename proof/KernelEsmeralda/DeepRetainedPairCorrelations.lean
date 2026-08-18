import KernelEsmeralda.ComplexBilinearNaturalScale
import KernelEsmeralda.FiniteBilinearGeometry
import KernelEsmeralda.DeepRetainedPairs

namespace KernelEsmeralda

noncomputable section

/-- Ordinary complex Poisson kernel between two zero ordinates. -/
def zetaFiniteCorrelationKernel
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (P.L T : ℂ) * P.Phi T
    (Zeta23.gammaOf (rho : Complex) - Zeta23.gammaOf (sigma : Complex))

/-- Conjugated-second complex Poisson kernel. -/
def zetaFiniteConjCorrelationKernel
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (P.L T : ℂ) * P.Phi T
    (Zeta23.gammaOf (rho : Complex) -
      starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex)))

/-- Two deep retained left representatives have all four finite real/imaginary
correlations determined, up to `L²/2`, by the two explicit complex Poisson
kernels `Phi(γρ-γσ)` and `Phi(γρ-conj γσ)`. -/
theorem zetaDeepRetainedLeftPairs_finite_correlations
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z s : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj)
    (hs : s ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    let sigma := zetaCarrierOfZI T s
    let gz := Zeta23.gammaOf (rho : Complex)
    let gs := Zeta23.gammaOf (sigma : Complex)
    let K := zetaFiniteCorrelationKernel P T rho sigma
    let Kc := zetaFiniteConjCorrelationKernel P T rho sigma
    |finiteRealRealCorrelation P T gz gs - (K.re + Kc.re)| ≤
        (P.L T) ^ 2 / 2 ∧
    |finiteImagImagCorrelation P T gz gs - (Kc.re - K.re)| ≤
        (P.L T) ^ 2 / 2 ∧
    |finiteRealImagCorrelation P T gz gs - (K.im - Kc.im)| ≤
        (P.L T) ^ 2 / 2 ∧
    |finiteImagRealCorrelation P T gz gs - (K.im + Kc.im)| ≤
        (P.L T) ^ 2 / 2 := by
  dsimp
  have hzmem := (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz
  have hsmem := (mem_zetaDeepRetainedLeftPairs_iff T P hconj s).mp hs
  have hzg := hzmem.2
  have hsg := hsmem.2
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  let sigma : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T s
  have hrhoL : T + Zeta23.D0 T ≤ (rho : Complex).im := by
    change T + Zeta23.D0 T ≤ (z : Complex).im
    exact hzg.1
  have hrhoR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T := by
    change (z : Complex).im ≤ 2 * T - Zeta23.D0 T
    exact hzg.2.1
  have hsigmaL : T + Zeta23.D0 T ≤ (sigma : Complex).im := by
    change T + Zeta23.D0 T ≤ (s : Complex).im
    exact hsg.1
  have hsigmaR : (sigma : Complex).im ≤ 2 * T - Zeta23.D0 T := by
    change (s : Complex).im ≤ 2 * T - Zeta23.D0 T
    exact hsg.2.1
  have hrhoTail :
      zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2 := by
    simpa [rho] using hzg.2.2.2
  have hsigmaTail :
      zetaNaturalCompressionTail P T sigma ≤ (P.L T) ^ 2 / 2 := by
    simpa [sigma] using hsg.2.2.2
  let gz : ℂ := Zeta23.gammaOf (rho : Complex)
  let gs : ℂ := Zeta23.gammaOf (sigma : Complex)
  let K : ℂ := zetaFiniteCorrelationKernel P T rho sigma
  let Kc : ℂ := zetaFiniteConjCorrelationKernel P T rho sigma
  have hB0 := zetaZeros_finiteComplexBilinear_error_le_quarter_L_sq
    P T hP hwL rho sigma hT
      hrhoL hrhoR hsigmaL hsigmaR hrhoTail hsigmaTail
  have hB : ‖finiteComplexBilinearSum P T gz gs - K‖ ≤
      (P.L T) ^ 2 / 4 := by
    simpa [gz, gs, K, zetaFiniteCorrelationKernel] using hB0
  have hBc0 := zetaZeros_finiteComplexBilinear_conj_error_le_quarter_L_sq
    P T hP hwL rho sigma hT
      hrhoL hrhoR hsigmaL hsigmaR hrhoTail hsigmaTail
  have hBc : ‖finiteComplexConjBilinearSum P T gz gs - Kc‖ ≤
      (P.L T) ^ 2 / 4 := by
    rw [← finiteComplexBilinearSum_conj_second P T gz gs]
    simpa [gz, gs, Kc, zetaFiniteConjCorrelationKernel] using hBc0
  have hRR0 := finiteRealRealCorrelation_error_le
    P T gz gs K Kc hB hBc
  have hII0 := finiteImagImagCorrelation_error_le
    P T gz gs K Kc hB hBc
  have hRI0 := finiteRealImagCorrelation_error_le
    P T gz gs K Kc hB hBc
  have hIR0 := finiteImagRealCorrelation_error_le
    P T gz gs K Kc hB hBc
  have hRR :
      |finiteRealRealCorrelation P T gz gs - (K.re + Kc.re)| ≤
        (P.L T) ^ 2 / 2 := by
    convert hRR0 using 1 <;> ring
  have hII :
      |finiteImagImagCorrelation P T gz gs - (Kc.re - K.re)| ≤
        (P.L T) ^ 2 / 2 := by
    convert hII0 using 1 <;> ring
  have hRI :
      |finiteRealImagCorrelation P T gz gs - (K.im - Kc.im)| ≤
        (P.L T) ^ 2 / 2 := by
    convert hRI0 using 1 <;> ring
  have hIR :
      |finiteImagRealCorrelation P T gz gs - (K.im + Kc.im)| ≤
        (P.L T) ^ 2 / 2 := by
    convert hIR0 using 1 <;> ring
  simpa [rho, sigma, gz, gs, K, Kc] using
    And.intro hRR (And.intro hII (And.intro hRI hIR))

end
end KernelEsmeralda
