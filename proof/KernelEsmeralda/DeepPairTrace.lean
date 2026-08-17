import KernelEsmeralda.DeepInteriorFiniteEnergy
import KernelEsmeralda.ZetaImPartEnergy

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- If every off-line pair representative in the chosen Zeta23 block is deep,
interior, and loses at most half of `L²` to compression, then the negative
`imPart` trace carries at least `L²/2` times the multiplicity mass of those
representatives. -/
theorem rtrace_zeta_imPart_ge_half_L_sq_mul_pair_mass
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData
      Zeta23.zetaZeroConfig T P hconj).PairReps)
    (hre : ∀ z ∈ R.R, (z : Complex).re ≤ 1 / 2)
    (hordL : ∀ z ∈ R.R,
      T + Zeta23.D0 T ≤ (z : Complex).im)
    (hordR : ∀ z ∈ R.R,
      (z : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hdeep : ∀ z ∈ R.R,
      2 * P.L T ≤
        (P.w / 2) * Real.exp
          ((1 - 2 * (z : Complex).re) *
            (P.L T / 2 - 3 * P.w / 2)))
    (htail : ∀ z ∈ R.R,
      zetaNaturalCompressionTail P T z ≤ (P.L T) ^ 2 / 2) :
    (∑ z ∈ R.R, (Zeta23.zetaZeroConfig.mult z : ℝ)) *
        ((P.L T) ^ 2 / 2) ≤
      rtrace ((Zeta23.ZeroSide.blockData
        Zeta23.zetaZeroConfig T P hconj).imPart R) := by
  rw [rtrace_zeta_imPart_eq_weighted_finiteImaginaryEnergy
    Zeta23.zetaZeroConfig T P hconj R]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z hz
  have hE := zeta_zero_left_half_deep_interior_finiteImaginaryEnergy_lower
    P T hP hwL z hT (hre z hz) (hordL z hz) (hordR z hz) (hdeep z hz)
  have hhalf :
      (P.L T) ^ 2 / 2 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
    linarith [htail z hz]
  exact mul_le_mul_of_nonneg_left hhalf (by positivity)

end
end KernelEsmeralda
