import KernelEsmeralda.OffLineComplexEnergy
import KernelEsmeralda.FiniteImaginaryEnergy
import Zeta23.Taper.Params

namespace KernelEsmeralda

noncomputable section

/-- A left-half nontrivial zeta zero forces a quantitative lower bound for the
full imaginary Poisson energy.  The taper edge supplies the growing term;
`a(T) ≤ 1` controls the critical-line baseline exactly enough for subtraction. -/
theorem zeta_zero_left_half_full_imaginary_energy_lower
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hre : (rho : Complex).re ≤ 1 / 2) :
    P.L T *
        ((P.w / 2) *
            Real.exp
              ((1 - 2 * (rho : Complex).re) *
                (P.L T / 2 - 3 * P.w / 2)) -
          P.L T) ≤
      fullImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
  have hL : 0 ≤ P.L T := by
    linarith [hP.one_le_w]
  have hphi := zeta_zero_left_half_complex_energy_lower
    P T hP hwL rho hre
  have ha := Zeta23.Params.a_le_one (P := P) (T := T) hP hwL
  have haL :
      P.a T * (P.L T) ^ 2 ≤ (P.L T) ^ 2 := by
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg (P.L T))
    simpa using this
  unfold fullImaginaryEnergy
  nlinarith

/-- If the edge contribution is at least twice the baseline length, then one
left-half zero contributes at least `L²` units of full imaginary energy.  This
is a convenient division-free notion of a sufficiently deep zero. -/
theorem zeta_zero_left_half_full_imaginary_energy_ge_L_sq
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hre : (rho : Complex).re ≤ 1 / 2)
    (hdeep :
      2 * P.L T ≤
        (P.w / 2) *
          Real.exp
            ((1 - 2 * (rho : Complex).re) *
              (P.L T / 2 - 3 * P.w / 2))) :
    (P.L T) ^ 2 ≤
      fullImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
  have hL : 0 ≤ P.L T := by
    linarith [hP.one_le_w]
  have hlower := zeta_zero_left_half_full_imaginary_energy_lower
    P T hP hwL rho hre
  have hedge :
      P.L T ≤
        (P.w / 2) *
            Real.exp
              ((1 - 2 * (rho : Complex).re) *
                (P.L T / 2 - 3 * P.w / 2)) -
          P.L T := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hedge hL
  nlinarith

end
end KernelEsmeralda
