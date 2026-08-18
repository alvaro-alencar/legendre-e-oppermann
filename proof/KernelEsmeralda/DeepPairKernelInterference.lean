import KernelEsmeralda.OffLineInterferenceSplit
import KernelEsmeralda.HyperbolicKernelInteraction

namespace KernelEsmeralda

noncomputable section

/-- The ideal kernel expression governing the contribution of the pair
`sigma` along the imaginary direction attached to `rho`. -/
def zetaIdealImagRayInteraction
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) : ℝ :=
  let K := zetaFiniteCorrelationKernel P T rho sigma
  let Kc := zetaFiniteConjCorrelationKernel P T rho sigma
  (K.im + Kc.im) ^ 2 - (Kc.re - K.re) ^ 2

/-- Elementary perturbation estimate for a square. -/
theorem abs_sq_sub_sq_le_of_abs_sub_le
    {x a δ : ℝ} (hδ : 0 ≤ δ) (h : |x - a| ≤ δ) :
    |x ^ 2 - a ^ 2| ≤ δ * (2 * |a| + δ) := by
  rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring, abs_mul]
  have hxa : |x + a| ≤ |x - a| + 2 * |a| := by
    calc
      |x + a| = |(x - a) + 2 * a| := by congr 1 <;> ring
      _ ≤ |x - a| + |2 * a| := abs_add_le _ _
      _ = |x - a| + 2 * |a| := by rw [abs_mul]; norm_num
  have hxa' : |x + a| ≤ δ + 2 * |a| := by
    exact hxa.trans (add_le_add_right h _)
  calc
    |x - a| * |x + a| ≤ δ * (δ + 2 * |a|) :=
      mul_le_mul h hxa' (abs_nonneg _) hδ
    _ = δ * (2 * |a| + δ) := by ring

/-- Two componentwise approximation bounds control the hyperbolic Rayleigh
interaction `IR² - II²`. -/
theorem abs_rayInteraction_sub_ideal_le
    {IR II IR0 II0 δ : ℝ}
    (hδ : 0 ≤ δ)
    (hIR : |IR - IR0| ≤ δ)
    (hII : |II - II0| ≤ δ) :
    |(IR ^ 2 - II ^ 2) - (IR0 ^ 2 - II0 ^ 2)| ≤
      δ * (2 * |IR0| + δ) + δ * (2 * |II0| + δ) := by
  have h1 := abs_sq_sub_sq_le_of_abs_sub_le hδ hIR
  have h2 := abs_sq_sub_sq_le_of_abs_sub_le hδ hII
  have ht := abs_sub_le (IR ^ 2 - IR0 ^ 2) (II ^ 2 - II0 ^ 2)
  have h := ht.trans (add_le_add h1 h2)
  convert h using 1 <;> ring

/-- For two deep retained left representatives, the finite Rayleigh
interaction is explicitly approximated by the two Poisson kernels. -/
theorem zetaDeepRetainedLeftPairs_rayInteraction_kernel_error
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z s : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj)
    (hs : s ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    let sigma := zetaCarrierOfZI T s
    let K := zetaFiniteCorrelationKernel P T rho sigma
    let Kc := zetaFiniteConjCorrelationKernel P T rho sigma
    let δ := (P.L T) ^ 2 / 2
    |(finiteImagRealCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) ^ 2 -
        finiteImagImagCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) ^ 2) -
      zetaIdealImagRayInteraction P T rho sigma| ≤
      δ * (2 * |K.im + Kc.im| + δ) +
        δ * (2 * |Kc.re - K.re| + δ) := by
  dsimp
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  let sigma : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T s
  let K : ℂ := zetaFiniteCorrelationKernel P T rho sigma
  let Kc : ℂ := zetaFiniteConjCorrelationKernel P T rho sigma
  let δ : ℝ := (P.L T) ^ 2 / 2
  obtain ⟨hRR, hII, hRI, hIR⟩ :=
    zetaDeepRetainedLeftPairs_finite_correlations
      T P hP hwL hT hconj z s hz hs
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hcore := abs_rayInteraction_sub_ideal_le hδ hIR hII
  simpa [rho, sigma, K, Kc, δ, zetaIdealImagRayInteraction] using hcore

/-- Weighted version: the actual pair interference term differs from its
kernel model by the same error multiplied by `m_sigma / 2`. -/
theorem zetaDeepRetainedLeftPairs_weightedInterference_kernel_error
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z s : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj)
    (hs : s ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    let sigma := zetaCarrierOfZI T s
    let K := zetaFiniteCorrelationKernel P T rho sigma
    let Kc := zetaFiniteConjCorrelationKernel P T rho sigma
    let δ := (P.L T) ^ 2 / 2
    |zetaImagRayPairInterference P T rho s -
        (Zeta23.zetaZeroConfig.mult sigma : ℝ) / 2 *
          zetaIdealImagRayInteraction P T rho sigma| ≤
      (Zeta23.zetaZeroConfig.mult sigma : ℝ) / 2 *
        (δ * (2 * |K.im + Kc.im| + δ) +
          δ * (2 * |Kc.re - K.re| + δ)) := by
  dsimp
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  let sigma : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T s
  let K : ℂ := zetaFiniteCorrelationKernel P T rho sigma
  let Kc : ℂ := zetaFiniteConjCorrelationKernel P T rho sigma
  let δ : ℝ := (P.L T) ^ 2 / 2
  have hcore := zetaDeepRetainedLeftPairs_rayInteraction_kernel_error
    T P hP hwL hT hconj z s hz hs
  have hm0 : 0 ≤ (Zeta23.zetaZeroConfig.mult sigma : ℝ) / 2 := by positivity
  unfold zetaImagRayPairInterference
  change
    |(Zeta23.zetaZeroConfig.mult sigma : ℝ) / 2 *
        ((finiteImagRealCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2 -
          finiteImagImagCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2) -
          zetaIdealImagRayInteraction P T rho sigma)| ≤ _
  rw [abs_mul, abs_of_nonneg hm0]
  exact mul_le_mul_of_nonneg_left
    (by simpa [rho, sigma, K, Kc, δ] using hcore) hm0

end
end KernelEsmeralda
