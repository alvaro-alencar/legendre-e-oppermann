import KernelEsmeralda.DeepPairTrace

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A partial version of the deep-pair trace estimate.

Only the selected subset `S` of off-line pair representatives needs to be
interior, deep, and well retained by the finite compression.  Every omitted
representative contributes nonnegative finite imaginary energy, so the full
`imPart` trace still dominates the multiplicity mass carried by `S`.
-/
theorem rtrace_zeta_imPart_ge_half_L_sq_mul_deep_subset_mass
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData
      Zeta23.zetaZeroConfig T P hconj).PairReps)
    (S : Finset (Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T))
    (hS : S ⊆ R.R)
    (hre : ∀ z ∈ S, (z : Complex).re ≤ 1 / 2)
    (hordL : ∀ z ∈ S,
      T + Zeta23.D0 T ≤ (z : Complex).im)
    (hordR : ∀ z ∈ S,
      (z : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hdeep : ∀ z ∈ S,
      2 * P.L T ≤
        (P.w / 2) * Real.exp
          ((1 - 2 * (z : Complex).re) *
            (P.L T / 2 - 3 * P.w / 2)))
    (htail : ∀ z ∈ S,
      zetaNaturalCompressionTail P T (zetaCarrierOfZI T z) ≤
        (P.L T) ^ 2 / 2) :
    (∑ z ∈ S, (Zeta23.zetaZeroConfig.mult z : ℝ)) *
        ((P.L T) ^ 2 / 2) ≤
      rtrace ((Zeta23.ZeroSide.blockData
        Zeta23.zetaZeroConfig T P hconj).imPart R) := by
  rw [rtrace_zeta_imPart_eq_weighted_finiteImaginaryEnergy
    Zeta23.zetaZeroConfig T P hconj R]
  rw [Finset.sum_mul]
  have hselected :
      ∑ z ∈ S,
          (Zeta23.zetaZeroConfig.mult z : ℝ) * ((P.L T) ^ 2 / 2) ≤
        ∑ z ∈ S,
          (Zeta23.zetaZeroConfig.mult z : ℝ) *
            finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
    apply Finset.sum_le_sum
    intro z hz
    let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
    have hE :
        (P.L T) ^ 2 - zetaNaturalCompressionTail P T rho ≤
          finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
      simpa [rho] using
        zeta_zero_left_half_deep_interior_finiteImaginaryEnergy_lower
          P T hP hwL rho hT (hre z hz) (hordL z hz) (hordR z hz) (hdeep z hz)
    have htail' :
        zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2 := by
      simpa [rho] using htail z hz
    have hhalf :
        (P.L T) ^ 2 / 2 ≤
          finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
      linarith [hE, htail']
    exact mul_le_mul_of_nonneg_left hhalf (by positivity)
  apply hselected.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro z hzR hzS
  exact mul_nonneg (by positivity) (by
    unfold finiteImaginaryEnergy
    positivity)

end
end KernelEsmeralda
