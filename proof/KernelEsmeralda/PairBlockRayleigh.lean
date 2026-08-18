import KernelEsmeralda.ZetaPairBlockFrobenius
import KernelEsmeralda.DeepRetainedFiniteGeometry

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Real quadratic form associated with a real matrix. -/
def realQuadraticForm (A : Matrix d d ℝ) (v : d → ℝ) : ℝ :=
  ∑ i : d, ∑ j : d, v i * A i j * v j

/-- A real rank-one matrix evaluates as the square of the corresponding dot
product. -/
theorem realQuadraticForm_vecMulVec_self
    (x v : d → ℝ) :
    realQuadraticForm (vecMulVec x x) v =
      (∑ i : d, v i * x i) ^ 2 := by
  unfold realQuadraticForm
  simp only [vecMulVec_apply]
  calc
    (∑ i : d, ∑ j : d, v i * (x i * x j) * v j) =
        ∑ i : d, ∑ j : d, (v i * x i) * (v j * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : d, (v i * x i) * (∑ j : d, v j * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = (∑ i : d, v i * x i) * (∑ j : d, v j * x j) := by
      rw [Finset.sum_mul]
    _ = (∑ i : d, v i * x i) ^ 2 := by ring

/-- Quadratic forms respect subtraction. -/
theorem realQuadraticForm_sub
    (A B : Matrix d d ℝ) (v : d → ℝ) :
    realQuadraticForm (A - B) v =
      realQuadraticForm A v - realQuadraticForm B v := by
  unfold realQuadraticForm
  simp only [Matrix.sub_apply]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Scalar factor for a quadratic form. -/
theorem realQuadraticForm_smul
    (a : ℝ) (A : Matrix d d ℝ) (v : d → ℝ) :
    realQuadraticForm (a • A) v = a * realQuadraticForm A v := by
  unfold realQuadraticForm
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i : d, ∑ j : d, v i * (a * A i j) * v j) =
        ∑ i : d, ∑ j : d, a * (v i * A i j * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = a * (∑ i : d, ∑ j : d, v i * A i j * v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Exact Rayleigh numerator of a real hyperbolic pair block. -/
theorem realQuadraticForm_hyperbolic_pair_block
    (m : ℝ) (x y v : d → ℝ) :
    realQuadraticForm (realHyperbolicPairBlock m x y) v =
      2 * m *
        ((∑ i : d, v i * x i) ^ 2 -
          (∑ i : d, v i * y i) ^ 2) := by
  unfold realHyperbolicPairBlock
  rw [realQuadraticForm_smul, realQuadraticForm_sub,
    realQuadraticForm_vecMulVec_self,
    realQuadraticForm_vecMulVec_self]
  ring

/-- Evaluating a pair block on its own imaginary vector is controlled by the
doubled cross and imaginary energies. -/
theorem realQuadraticForm_hyperbolic_pair_block_on_imag
    (m : ℝ) (x y : d → ℝ) :
    realQuadraticForm (realHyperbolicPairBlock m x y) y =
      m / 2 * (doubledDot x y ^ 2 - doubledDot y y ^ 2) := by
  rw [realQuadraticForm_hyperbolic_pair_block]
  have hxy : doubledDot x y = 2 * (∑ i : d, y i * x i) := by
    unfold doubledDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hyy : doubledDot y y = 2 * (∑ i : d, y i * y i) := by
    unfold doubledDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hxy, hyy]
  ring

/-- Exact interference of the pair of `sigma` on the imaginary direction of
`rho`: only the finite IR and II correlations occur. -/
theorem realQuadraticForm_zeta_pair_block_on_other_imag
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    realQuadraticForm
        (zetaRealHyperbolicPairBlock P T sigma)
        (zetaPairImagVector P T rho) =
      (Zeta23.zetaZeroConfig.mult sigma : ℝ) / 2 *
        (finiteImagRealCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2 -
          finiteImagImagCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2) := by
  unfold zetaRealHyperbolicPairBlock
  rw [realQuadraticForm_hyperbolic_pair_block]
  have hIR :
      finiteImagRealCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) =
        2 * (∑ i : Fin (P.d T),
          zetaPairImagVector P T rho i *
            zetaPairRealVector P T sigma i) := by
    rw [← doubledDot_zetaPairImagReal_eq_IR]
    unfold doubledDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hII :
      finiteImagImagCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) =
        2 * (∑ i : Fin (P.d T),
          zetaPairImagVector P T rho i *
            zetaPairImagVector P T sigma i) := by
    rw [← doubledDot_zetaPairImag_eq_II]
    unfold doubledDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hIR, hII]
  ring

/-- A deep retained pair has an explicit strongly negative direction: its own
imaginary sampled vector. -/
theorem zetaDeepRetainedLeftPair_negative_imag_direction
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    realQuadraticForm
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaPairImagVector P T rho) ≤
      -(3 / 32) * (Zeta23.zetaZeroConfig.mult rho : ℝ) *
        (P.L T) ^ 4 := by
  dsimp
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  obtain ⟨hEi, -, hEc⟩ :=
    zetaDeepRetainedLeftPair_finite_geometry
      T P hP hwL hT hconj z hz
  have hq := realQuadraticForm_zeta_pair_block_on_other_imag
    P T rho rho
  have hIR :
      finiteImagRealCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    unfold finiteImagRealCorrelation finiteCrossEnergy
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hII :
      finiteImagImagCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    rfl
  rw [hIR, hII] at hq
  have hEcBounds := abs_le.mp hEc
  have hEcSq :
      finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 ≤
        ((P.L T) ^ 2 / 4) ^ 2 := by
    have hB : 0 ≤ (P.L T) ^ 2 / 4 := by positivity
    have hleft : 0 ≤
        finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) +
          (P.L T) ^ 2 / 4 := by linarith [hEcBounds.1]
    have hright : 0 ≤
        (P.L T) ^ 2 / 4 -
          finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
      linarith [hEcBounds.2]
    nlinarith [mul_nonneg hleft hright]
  have hEi0 : 0 ≤ finiteImaginaryEnergy P T
      (Zeta23.gammaOf (rho : Complex)) := finiteImaginaryEnergy_nonneg _ _ _
  have hEiSq :
      ((P.L T) ^ 2 / 2) ^ 2 ≤
        finiteImaginaryEnergy P T
          (Zeta23.gammaOf (rho : Complex)) ^ 2 := by
    have hbase0 : 0 ≤ (P.L T) ^ 2 / 2 := by positivity
    have hdiff : 0 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
          (P.L T) ^ 2 / 2 := sub_nonneg.mpr hEi
    have hsum : 0 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) +
          (P.L T) ^ 2 / 2 := add_nonneg hEi0 hbase0
    nlinarith [mul_nonneg hdiff hsum]
  have hdiff :
      finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 -
          finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 ≤
        -(3 / 16) * (P.L T) ^ 4 := by
    nlinarith [hEcSq, hEiSq]
  have hm0 : 0 ≤ (Zeta23.zetaZeroConfig.mult rho : ℝ) := by positivity
  rw [hq]
  have hmul := mul_le_mul_of_nonneg_left hdiff (hm0 / 2)
  nlinarith

end
end KernelEsmeralda
