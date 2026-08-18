import KernelEsmeralda.PairBlockRayleigh
import KernelEsmeralda.ComplexSquareNaturalScale
import KernelEsmeralda.FullImaginaryEnergyDepth
import KernelEsmeralda.NaturalCompressionTail

namespace KernelEsmeralda

noncomputable section

/-- Explicit retained imaginary-energy lower bound for a left-half zero in the
natural `D₀ = √T` interior.  Unlike the boolean `deep` predicate, this keeps
the full exponential dependence on horizontal depth. -/
def zetaDepthImaginaryLower
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : ℝ :=
  P.L T *
      ((P.w / 2) *
          Real.exp
            ((1 - 2 * (rho : Complex).re) *
              (P.L T / 2 - 3 * P.w / 2)) -
        P.L T) -
    zetaNaturalCompressionTail P T rho

/-- Natural upper bound for the finite real-imaginary cross energy. -/
def zetaDepthCrossUpper
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : ℝ :=
  zetaNaturalSquareCompressionTail P T rho

/-- The finite imaginary energy retains the full continuous depth lower bound. -/
theorem zeta_zero_left_half_interior_finiteImaginaryEnergy_ge_depthLower
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hre : (rho : Complex).re ≤ 1 / 2)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T) :
    zetaDepthImaginaryLower P T rho ≤
      finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
  have hfull := zeta_zero_left_half_full_imaginary_energy_lower
    P T hP hwL rho hre
  have hfinite :=
    zetaZero_finiteImaginaryEnergy_ge_full_sub_D0_tail_of_one_le_T
      P T hP hwL rho hT hordL hordR
  change
    fullImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
      zetaNaturalCompressionTail P T rho ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) at hfinite
  unfold zetaDepthImaginaryLower
  linarith

/-- The finite real-imaginary cross energy is bounded by the natural square
compression tail, with no depth threshold. -/
theorem zeta_zero_interior_abs_finiteCrossEnergy_le_depthCrossUpper
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T) :
    |finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex))| ≤
      zetaDepthCrossUpper P T rho := by
  have herr := zetaZero_finiteComplexSquare_error_norm_le_D0_of_one_le_T
    P T hP hwL rho hT hordL hordR
  exact abs_finiteCrossEnergy_le_of_square_error
    P T (Zeta23.gammaOf (rho : Complex)) herr

/-- Continuous-depth Rayleigh estimate for one left-half zero.  Once the depth
lower bound is nonnegative, the pair's own imaginary direction pays the
explicit difference `Iρ² - Cρ²`. -/
theorem zeta_zero_left_half_interior_pairRayleigh_le_depth_gap
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hre : (rho : Complex).re ≤ 1 / 2)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hI0 : 0 ≤ zetaDepthImaginaryLower P T rho) :
    realQuadraticForm
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaPairImagVector P T rho) ≤
      (Zeta23.zetaZeroConfig.mult rho : ℝ) / 2 *
        (zetaDepthCrossUpper P T rho ^ 2 -
          zetaDepthImaginaryLower P T rho ^ 2) := by
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
  have hEi := zeta_zero_left_half_interior_finiteImaginaryEnergy_ge_depthLower
    P T hP hwL rho hT hre hordL hordR
  have hEc := zeta_zero_interior_abs_finiteCrossEnergy_le_depthCrossUpper
    P T hP hwL rho hT hordL hordR
  have hC0 : 0 ≤ zetaDepthCrossUpper P T rho := by
    unfold zetaDepthCrossUpper zetaNaturalSquareCompressionTail
    positivity
  have hEcBounds := abs_le.mp hEc
  have hEcSq :
      finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 ≤
        zetaDepthCrossUpper P T rho ^ 2 := by
    have hleft : 0 ≤
        finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) +
          zetaDepthCrossUpper P T rho := by linarith [hEcBounds.1]
    have hright : 0 ≤
        zetaDepthCrossUpper P T rho -
          finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
      linarith [hEcBounds.2]
    nlinarith [mul_nonneg hleft hright]
  have hEi0 : 0 ≤ finiteImaginaryEnergy P T
      (Zeta23.gammaOf (rho : Complex)) := finiteImaginaryEnergy_nonneg _ _ _
  have hEiSq :
      zetaDepthImaginaryLower P T rho ^ 2 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 := by
    have hdiff : 0 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
          zetaDepthImaginaryLower P T rho := sub_nonneg.mpr hEi
    have hsum : 0 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) +
          zetaDepthImaginaryLower P T rho := add_nonneg hEi0 hI0
    nlinarith [mul_nonneg hdiff hsum]
  have hgap :
      finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 -
          finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 ≤
        zetaDepthCrossUpper P T rho ^ 2 -
          zetaDepthImaginaryLower P T rho ^ 2 := by
    linarith
  have hm0 : 0 ≤ (Zeta23.zetaZeroConfig.mult rho : ℝ) / 2 := by positivity
  rw [hq]
  exact mul_le_mul_of_nonneg_left hgap hm0

/-- If the retained depth energy exceeds the cross-energy tail, the pair block
is strictly negative on its own imaginary sampled vector. -/
theorem zeta_zero_left_half_interior_pairRayleigh_neg_of_cross_lt_depth
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hre : (rho : Complex).re ≤ 1 / 2)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hI0 : 0 ≤ zetaDepthImaginaryLower P T rho)
    (hgap : zetaDepthCrossUpper P T rho <
      zetaDepthImaginaryLower P T rho) :
    realQuadraticForm
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaPairImagVector P T rho) < 0 := by
  have h := zeta_zero_left_half_interior_pairRayleigh_le_depth_gap
    P T hP hwL rho hT hre hordL hordR hI0
  have hmposNat := Zeta23.zetaZeroConfig.one_le_mult (rho : Complex) rho.property
  have hmpos : 0 < (Zeta23.zetaZeroConfig.mult rho : ℝ) / 2 := by
    have : (0 : ℝ) < Zeta23.zetaZeroConfig.mult rho := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmposNat)
    positivity
  have hC0 : 0 ≤ zetaDepthCrossUpper P T rho := by
    unfold zetaDepthCrossUpper zetaNaturalSquareCompressionTail
    positivity
  have hsq :
      zetaDepthCrossUpper P T rho ^ 2 <
        zetaDepthImaginaryLower P T rho ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hgap) (add_pos_of_nonneg_of_pos hC0 (lt_of_le_of_lt hI0 hgap))]
  have :
      (Zeta23.zetaZeroConfig.mult rho : ℝ) / 2 *
        (zetaDepthCrossUpper P T rho ^ 2 -
          zetaDepthImaginaryLower P T rho ^ 2) < 0 := by
    exact mul_neg_of_pos_of_neg hmpos (sub_neg.mpr hsq)
  exact lt_of_le_of_lt h this

end
end KernelEsmeralda
