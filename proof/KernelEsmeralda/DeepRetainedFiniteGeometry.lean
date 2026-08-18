import KernelEsmeralda.ComplexSquareNaturalScale
import KernelEsmeralda.DeepRetainedPairs

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Every deep retained left representative carries a quantitatively
well-conditioned real/imaginary geometry inside the actual finite Zeta23
compression:

* at least `L²/2` imaginary energy;
* at least `L²` real energy;
* cross energy at most `L²/4` in absolute value.

Thus the two real vectors forming the hyperbolic pair block cannot become
nearly collinear through finite-grid truncation. -/
theorem zetaDeepRetainedLeftPair_finite_geometry
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    (P.L T) ^ 2 / 2 ≤
        finiteImaginaryEnergy P T
          (Zeta23.gammaOf (z : Complex)) ∧
    (P.L T) ^ 2 ≤
        finiteRealEnergy P T
          (Zeta23.gammaOf (z : Complex)) ∧
    |finiteCrossEnergy P T
        (Zeta23.gammaOf (z : Complex))| ≤
      (P.L T) ^ 2 / 4 := by
  have hzmem := (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz
  have hzLeft := hzmem.1
  have hgood := hzmem.2
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hre : (rho : Complex).re ≤ 1 / 2 := by
    change (z : Complex).re ≤ 1 / 2
    exact zetaLeftPairReps_re_le_half T P hconj z hzLeft
  have hordL : T + Zeta23.D0 T ≤ (rho : Complex).im := by
    change T + Zeta23.D0 T ≤ (z : Complex).im
    exact hgood.1
  have hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T := by
    change (z : Complex).im ≤ 2 * T - Zeta23.D0 T
    exact hgood.2.1
  have hdeep :
      2 * P.L T ≤
        (P.w / 2) * Real.exp
          ((1 - 2 * (rho : Complex).re) *
            (P.L T / 2 - 3 * P.w / 2)) := by
    change
      2 * P.L T ≤
        (P.w / 2) * Real.exp
          ((1 - 2 * (z : Complex).re) *
            (P.L T / 2 - 3 * P.w / 2))
    exact hgood.2.2.1
  have htail :
      zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2 := by
    simpa [rho] using hgood.2.2.2
  have hfinite :=
    zeta_zero_left_half_deep_interior_finiteImaginaryEnergy_lower
      P T hP hwL rho hT hre hordL hordR hdeep
  have himag :
      (P.L T) ^ 2 / 2 ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    linarith [hfinite, htail]
  have herr :=
    zetaZero_finiteComplexSquare_error_norm_le_quarter_L_sq
      P T hP hwL rho hT hordL hordR htail
  have hcross :=
    abs_finiteCrossEnergy_le_of_square_error
      P T (Zeta23.gammaOf (rho : Complex)) herr
  have hdiff0 :=
    abs_real_sub_imag_sub_baseline_le_of_square_error
      P T (Zeta23.gammaOf (rho : Complex)) herr
  have hdiff :
      |finiteRealEnergy P T (Zeta23.gammaOf (rho : Complex)) -
          finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
          2 * (P.a T * P.L T ^ 2)| ≤
        (P.L T) ^ 2 / 2 := by
    convert hdiff0 using 1 <;> ring
  have hdiffLower := (abs_le.mp hdiff).1
  have ha := Zeta23.Params.half_le_a (P := P) (T := T) hP hwL
  have hL2 : 0 ≤ (P.L T) ^ 2 := sq_nonneg _
  have hamul := mul_le_mul_of_nonneg_right ha hL2
  have habase :
      (P.L T) ^ 2 ≤ 2 * (P.a T * P.L T ^ 2) := by
    nlinarith
  have hreal :
      (P.L T) ^ 2 ≤
        finiteRealEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    nlinarith [himag, hdiffLower, habase]
  simpa [rho] using And.intro himag (And.intro hreal hcross)

end
end KernelEsmeralda
