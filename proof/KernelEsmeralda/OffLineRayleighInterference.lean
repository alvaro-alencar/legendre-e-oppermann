import KernelEsmeralda.PairBlockRayleigh
import KernelEsmeralda.LeftPairReps

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Real sum of all hyperbolic pair blocks for a chosen representative system. -/
def zetaRealOffLinePairBlockSum
    (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData
      Zeta23.zetaZeroConfig T P hconj).PairReps) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℝ :=
  ∑ s ∈ R.R,
    zetaRealHyperbolicPairBlock P T (zetaCarrierOfZI T s)

/-- Quadratic forms are additive. -/
theorem realQuadraticForm_add
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℝ) (v : d → ℝ) :
    realQuadraticForm (A + B) v =
      realQuadraticForm A v + realQuadraticForm B v := by
  unfold realQuadraticForm
  simp only [Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Quadratic form of a finite sum is the sum of quadratic forms. -/
theorem realQuadraticForm_finset_sum
    {d ι : Type*} [Fintype d] [DecidableEq d]
    (S : Finset ι) (F : ι → Matrix d d ℝ) (v : d → ℝ) :
    realQuadraticForm (∑ s ∈ S, F s) v =
      ∑ s ∈ S, realQuadraticForm (F s) v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [realQuadraticForm]
  | @insert a S ha ih =>
      simp [ha, realQuadraticForm_add, ih]

/-- Exact total off-line interference along the imaginary direction of an
arbitrary zeta zero. -/
theorem realQuadraticForm_zetaRealOffLinePairBlockSum_on_imag
    (P : Zeta23.Params) (T : ℝ)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData
      Zeta23.zetaZeroConfig T P hconj).PairReps)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    realQuadraticForm
        (zetaRealOffLinePairBlockSum P T hconj R)
        (zetaPairImagVector P T rho) =
      ∑ s ∈ R.R,
        (Zeta23.zetaZeroConfig.mult (zetaCarrierOfZI T s) : ℝ) / 2 *
          (finiteImagRealCorrelation P T
              (Zeta23.gammaOf (rho : Complex))
              (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2 -
            finiteImagImagCorrelation P T
              (Zeta23.gammaOf (rho : Complex))
              (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2) := by
  unfold zetaRealOffLinePairBlockSum
  rw [realQuadraticForm_finset_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact realQuadraticForm_zeta_pair_block_on_other_imag
    P T rho (zetaCarrierOfZI T s)

/-- For the canonical left representatives, the total off-line quadratic form
splits into the selected pair's strongly negative self contribution plus the
interference from every other reflection pair. -/
theorem zetaDeepRetainedLeftPair_offLineRayleigh_split
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let R := zetaLeftPairReps T P hconj
    let rho := zetaCarrierOfZI T z
    realQuadraticForm
        (zetaRealOffLinePairBlockSum P T hconj R)
        (zetaPairImagVector P T rho) =
      realQuadraticForm
          (zetaRealHyperbolicPairBlock P T rho)
          (zetaPairImagVector P T rho) +
        ∑ s ∈ R.R.erase z,
          (Zeta23.zetaZeroConfig.mult (zetaCarrierOfZI T s) : ℝ) / 2 *
            (finiteImagRealCorrelation P T
                (Zeta23.gammaOf (rho : Complex))
                (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                  Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2 -
              finiteImagImagCorrelation P T
                (Zeta23.gammaOf (rho : Complex))
                (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                  Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2) := by
  dsimp
  let R := zetaLeftPairReps T P hconj
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hzR : z ∈ R.R := by
    exact (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.1
  rw [realQuadraticForm_zetaRealOffLinePairBlockSum_on_imag
    P T hconj R rho]
  rw [← Finset.add_sum_erase _ _ hzR]
  have hself := realQuadraticForm_zeta_pair_block_on_other_imag P T rho rho
  change
    (Zeta23.zetaZeroConfig.mult rho : ℝ) / 2 *
        (finiteImagRealCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (rho : Complex)) ^ 2 -
          finiteImagImagCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (rho : Complex)) ^ 2) + _ = _
  rw [← hself]
  rfl

/-- If the off-diagonal pair interference is smaller than the certified self
penalty, then the total off-line pair block remains negative on the selected
imaginary direction. -/
theorem zetaDeepRetainedLeftPair_offLine_negative_of_interference_lt
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj)
    (hinterf :
      let R := zetaLeftPairReps T P hconj
      let rho := zetaCarrierOfZI T z
      (∑ s ∈ R.R.erase z,
          (Zeta23.zetaZeroConfig.mult (zetaCarrierOfZI T s) : ℝ) / 2 *
            (finiteImagRealCorrelation P T
                (Zeta23.gammaOf (rho : Complex))
                (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                  Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2 -
              finiteImagImagCorrelation P T
                (Zeta23.gammaOf (rho : Complex))
                (Zeta23.gammaOf ((zetaCarrierOfZI T s :
                  Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2)) <
        3 / 32 * (Zeta23.zetaZeroConfig.mult rho : ℝ) *
          (P.L T) ^ 4) :
    let R := zetaLeftPairReps T P hconj
    let rho := zetaCarrierOfZI T z
    realQuadraticForm
        (zetaRealOffLinePairBlockSum P T hconj R)
        (zetaPairImagVector P T rho) < 0 := by
  dsimp at hinterf ⊢
  let R := zetaLeftPairReps T P hconj
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hsplit := zetaDeepRetainedLeftPair_offLineRayleigh_split
    T P hP hwL hT hconj z hz
  have hself := zetaDeepRetainedLeftPair_negative_imag_direction
    T P hP hwL hT hconj z hz
  dsimp [R, rho] at hsplit hinterf hself ⊢
  rw [hsplit]
  linarith

end
end KernelEsmeralda
