import KernelEsmeralda.DeepInteriorFiniteEnergy
import KernelEsmeralda.ZetaImPartEnergy

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A zero in the finite Zeta23 window, lifted back to the ambient zeta zero
configuration together with the carrier-membership proof already encoded by `ZI`. -/
def zetaCarrierOfZI (T : ℝ)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :
    Zeta23.zetaZeroConfig.carrier :=
  ⟨(z : Complex),
    Zeta23.ZeroSide.mem_carrier_of_mem_ZI
      Zeta23.zetaZeroConfig T z.2⟩

@[simp] theorem coe_zetaCarrierOfZI (T : ℝ)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :
    ((zetaCarrierOfZI T z : Zeta23.zetaZeroConfig.carrier) : Complex) =
      (z : Complex) := rfl

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
      zetaNaturalCompressionTail P T (zetaCarrierOfZI T z) ≤
        (P.L T) ^ 2 / 2) :
    (∑ z ∈ R.R, (Zeta23.zetaZeroConfig.mult z : ℝ)) *
        ((P.L T) ^ 2 / 2) ≤
      rtrace ((Zeta23.ZeroSide.blockData
        Zeta23.zetaZeroConfig T P hconj).imPart R) := by
  rw [rtrace_zeta_imPart_eq_weighted_finiteImaginaryEnergy
    Zeta23.zetaZeroConfig T P hconj R]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z hz
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hrho : (rho : Complex) = (z : Complex) := by
    rfl
  have hE :
      (P.L T) ^ 2 - zetaNaturalCompressionTail P T rho ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
    simpa [rho, hrho] using
      zeta_zero_left_half_deep_interior_finiteImaginaryEnergy_lower
        P T hP hwL rho hT (hre z hz) (hordL z hz) (hordR z hz) (hdeep z hz)
  have hhalf :
      (P.L T) ^ 2 / 2 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex)) := by
    have htail' : zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2 := by
      simpa [rho] using htail z hz
    linarith [hE, htail']
  exact mul_le_mul_of_nonneg_left hhalf (by positivity)

end
end KernelEsmeralda
