import KernelEsmeralda.ComplexBilinearCompressionError
import KernelEsmeralda.ComplexSquareNaturalScale

namespace KernelEsmeralda

noncomputable section

/-- Natural `D₀ = √T` square-tail expression for an arbitrary complex
argument. -/
def naturalSquareCompressionTailAt
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
      ((((Zeta23.D0 T) + P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) + P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T)) +
  (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
      ((((Zeta23.D0 T) - P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) - P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T))

@[simp] theorem naturalSquareCompressionTailAt_conj
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    naturalSquareCompressionTailAt P T (starRingEnd ℂ z) =
      naturalSquareCompressionTailAt P T z := by
  unfold naturalSquareCompressionTailAt imaginaryEnergyDecayEnvelope
  simp

/-- The zeta-specific natural square tail is the generic expression evaluated
at `γ_ρ`. -/
theorem naturalSquareCompressionTailAt_gammaOf
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    naturalSquareCompressionTailAt P T (Zeta23.gammaOf (rho : Complex)) =
      zetaNaturalSquareCompressionTail P T rho := by
  rfl

/-- Natural-scale version of the finite bilinear compression estimate. -/
theorem finiteComplexBilinear_error_norm_le_D0_of_one_le_T
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) (hT : 1 ≤ T)
    (hzL : T + Zeta23.D0 T ≤ z.re)
    (hzR : z.re ≤ 2 * T - Zeta23.D0 T)
    (hwLeft : T + Zeta23.D0 T ≤ w.re)
    (hwRight : w.re ≤ 2 * T - Zeta23.D0 T) :
    ‖finiteComplexBilinearSum P T z w -
        ((P.L T : ℂ) * P.Phi T (z - w))‖ ≤
      (naturalSquareCompressionTailAt P T z +
        naturalSquareCompressionTailAt P T w) / 2 := by
  have hD : 0 < Zeta23.D0 T := by
    unfold Zeta23.D0
    exact Real.sqrt_pos.2 (zero_lt_one.trans_le hT)
  have hhD := zeta23_hgrid_lt_D0_of_one_le_T P T hP hwL hT
  have h := finiteComplexBilinear_error_norm_le_interior
    P T (Zeta23.D0 T) hP hwL z w hD hhD
      hzL hzR hwLeft hwRight
  unfold naturalSquareCompressionTailAt
  convert h using 1 <;> ring

/-- A retained zeta zero has generic natural square tail at most `L²/4`. -/
theorem naturalSquareCompressionTailAt_gammaOf_le_quarter_L_sq
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (htail : zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2) :
    naturalSquareCompressionTailAt P T (Zeta23.gammaOf (rho : Complex)) ≤
      (P.L T) ^ 2 / 4 := by
  rw [naturalSquareCompressionTailAt_gammaOf]
  have hrel := two_mul_zetaNaturalSquareCompressionTail P T rho
  linarith

/-- Bilinear finite correlation of two retained interior zeta zeros differs
from the exact complex Poisson kernel by at most `L²/4`. -/
theorem zetaZeros_finiteComplexBilinear_error_le_quarter_L_sq
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho sigma : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hrhoL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hrhoR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hsigmaL : T + Zeta23.D0 T ≤ (sigma : Complex).im)
    (hsigmaR : (sigma : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hrhoTail : zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2)
    (hsigmaTail : zetaNaturalCompressionTail P T sigma ≤ (P.L T) ^ 2 / 2) :
    ‖finiteComplexBilinearSum P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) -
        ((P.L T : ℂ) * P.Phi T
          (Zeta23.gammaOf (rho : Complex) -
            Zeta23.gammaOf (sigma : Complex)))‖ ≤
      (P.L T) ^ 2 / 4 := by
  have hzL : T + Zeta23.D0 T ≤
      (Zeta23.gammaOf (rho : Complex)).re := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hrhoL
  have hzR : (Zeta23.gammaOf (rho : Complex)).re ≤
      2 * T - Zeta23.D0 T := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hrhoR
  have hwLeft : T + Zeta23.D0 T ≤
      (Zeta23.gammaOf (sigma : Complex)).re := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hsigmaL
  have hwRight : (Zeta23.gammaOf (sigma : Complex)).re ≤
      2 * T - Zeta23.D0 T := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hsigmaR
  have h := finiteComplexBilinear_error_norm_le_D0_of_one_le_T
    P T hP hwL
      (Zeta23.gammaOf (rho : Complex))
      (Zeta23.gammaOf (sigma : Complex)) hT
      hzL hzR hwLeft hwRight
  have hr := naturalSquareCompressionTailAt_gammaOf_le_quarter_L_sq
    P T rho hrhoTail
  have hs := naturalSquareCompressionTailAt_gammaOf_le_quarter_L_sq
    P T sigma hsigmaTail
  calc
    ‖finiteComplexBilinearSum P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (sigma : Complex)) -
        ((P.L T : ℂ) * P.Phi T
          (Zeta23.gammaOf (rho : Complex) -
            Zeta23.gammaOf (sigma : Complex)))‖
        ≤ (naturalSquareCompressionTailAt P T
              (Zeta23.gammaOf (rho : Complex)) +
            naturalSquareCompressionTailAt P T
              (Zeta23.gammaOf (sigma : Complex))) / 2 := h
    _ ≤ (P.L T) ^ 2 / 4 := by linarith

/-- The same `L²/4` control holds for the conjugated second sampled vector,
which is the second kernel needed to resolve real/imaginary cross-correlations. -/
theorem zetaZeros_finiteComplexBilinear_conj_error_le_quarter_L_sq
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho sigma : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hrhoL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hrhoR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hsigmaL : T + Zeta23.D0 T ≤ (sigma : Complex).im)
    (hsigmaR : (sigma : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hrhoTail : zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2)
    (hsigmaTail : zetaNaturalCompressionTail P T sigma ≤ (P.L T) ^ 2 / 2) :
    ‖finiteComplexBilinearSum P T
          (Zeta23.gammaOf (rho : Complex))
          (starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))) -
        ((P.L T : ℂ) * P.Phi T
          (Zeta23.gammaOf (rho : Complex) -
            starRingEnd ℂ (Zeta23.gammaOf (sigma : Complex))))‖ ≤
      (P.L T) ^ 2 / 4 := by
  let z := Zeta23.gammaOf (rho : Complex)
  let w := Zeta23.gammaOf (sigma : Complex)
  have hzL : T + Zeta23.D0 T ≤ z.re := by
    dsimp [z]
    rw [zeta23_gammaOf_re_eq_im]
    exact hrhoL
  have hzR : z.re ≤ 2 * T - Zeta23.D0 T := by
    dsimp [z]
    rw [zeta23_gammaOf_re_eq_im]
    exact hrhoR
  have hwLeft0 : T + Zeta23.D0 T ≤ w.re := by
    dsimp [w]
    rw [zeta23_gammaOf_re_eq_im]
    exact hsigmaL
  have hwRight0 : w.re ≤ 2 * T - Zeta23.D0 T := by
    dsimp [w]
    rw [zeta23_gammaOf_re_eq_im]
    exact hsigmaR
  have hwLeft : T + Zeta23.D0 T ≤ (starRingEnd ℂ w).re := by
    simpa using hwLeft0
  have hwRight : (starRingEnd ℂ w).re ≤ 2 * T - Zeta23.D0 T := by
    simpa using hwRight0
  have h := finiteComplexBilinear_error_norm_le_D0_of_one_le_T
    P T hP hwL z (starRingEnd ℂ w) hT
      hzL hzR hwLeft hwRight
  have hr := naturalSquareCompressionTailAt_gammaOf_le_quarter_L_sq
    P T rho hrhoTail
  have hs0 := naturalSquareCompressionTailAt_gammaOf_le_quarter_L_sq
    P T sigma hsigmaTail
  have hs : naturalSquareCompressionTailAt P T (starRingEnd ℂ w) ≤
      (P.L T) ^ 2 / 4 := by
    rw [naturalSquareCompressionTailAt_conj]
    simpa [w] using hs0
  change ‖finiteComplexBilinearSum P T z (starRingEnd ℂ w) -
      ((P.L T : ℂ) * P.Phi T (z - starRingEnd ℂ w))‖ ≤ _
  calc
    ‖finiteComplexBilinearSum P T z (starRingEnd ℂ w) -
        ((P.L T : ℂ) * P.Phi T (z - starRingEnd ℂ w))‖
        ≤ (naturalSquareCompressionTailAt P T z +
            naturalSquareCompressionTailAt P T (starRingEnd ℂ w)) / 2 := h
    _ ≤ (P.L T) ^ 2 / 4 := by
      have hr' : naturalSquareCompressionTailAt P T z ≤
          (P.L T) ^ 2 / 4 := by simpa [z] using hr
      linarith

end
end KernelEsmeralda
