import KernelEsmeralda.ComplexSquareCompressionError
import KernelEsmeralda.NaturalCompressionTail

namespace KernelEsmeralda

noncomputable section

/-- Natural `D₀ = √T` tail for the complex-square compression error.  It is
exactly half of the already-used imaginary-energy compression tail. -/
def zetaNaturalSquareCompressionTail
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : ℝ :=
  (imaginaryEnergyDecayEnvelope P T
    (Zeta23.gammaOf (rho : Complex))) ^ 2 *
      ((((Zeta23.D0 T) + P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) + P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T)) +
  (imaginaryEnergyDecayEnvelope P T
    (Zeta23.gammaOf (rho : Complex))) ^ 2 *
      ((((Zeta23.D0 T) - P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) - P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T))

/-- The square-compression tail is exactly half of the imaginary-energy tail. -/
theorem two_mul_zetaNaturalSquareCompressionTail
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    2 * zetaNaturalSquareCompressionTail P T rho =
      zetaNaturalCompressionTail P T rho := by
  unfold zetaNaturalSquareCompressionTail zetaNaturalCompressionTail
  ring

/-- For an actual zeta zero lying `D₀` inside the dyadic ordinate window, the
finite complex-square identity differs from its exact Poisson value by at most
the natural square-compression tail. -/
theorem zetaZero_finiteComplexSquare_error_norm_le_D0_of_one_le_T
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T) :
    ‖finiteComplexSquareSum P T (Zeta23.gammaOf (rho : Complex)) -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ ≤
      zetaNaturalSquareCompressionTail P T rho := by
  have hD : 0 < Zeta23.D0 T := by
    unfold Zeta23.D0
    exact Real.sqrt_pos.2 (zero_lt_one.trans_le hT)
  have hhD := zeta23_hgrid_lt_D0_of_one_le_T P T hP hwL hT
  have hzL :
      T + Zeta23.D0 T ≤
        (Zeta23.gammaOf (rho : Complex)).re := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordL
  have hzR :
      (Zeta23.gammaOf (rho : Complex)).re ≤
        2 * T - Zeta23.D0 T := by
    rw [zeta23_gammaOf_re_eq_im]
    exact hordR
  simpa [zetaNaturalSquareCompressionTail] using
    finiteComplexSquare_error_norm_le_interior
      P T (Zeta23.D0 T) hP hwL
      (Zeta23.gammaOf (rho : Complex)) hD hhD hzL hzR

/-- The retention condition already used by the deep-pair argument is twice
as strong as needed for a `L²/4` bound on the complex-square compression error. -/
theorem zetaZero_finiteComplexSquare_error_norm_le_quarter_L_sq
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (htail : zetaNaturalCompressionTail P T rho ≤ (P.L T) ^ 2 / 2) :
    ‖finiteComplexSquareSum P T (Zeta23.gammaOf (rho : Complex)) -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ ≤
      (P.L T) ^ 2 / 4 := by
  have herr := zetaZero_finiteComplexSquare_error_norm_le_D0_of_one_le_T
    P T hP hwL rho hT hordL hordR
  have hrel := two_mul_zetaNaturalSquareCompressionTail P T rho
  have hsq :
      zetaNaturalSquareCompressionTail P T rho ≤ (P.L T) ^ 2 / 4 := by
    linarith
  exact herr.trans hsq

end
end KernelEsmeralda
