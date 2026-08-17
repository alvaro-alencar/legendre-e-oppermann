import KernelEsmeralda.NaturalCompressionTail
import KernelEsmeralda.FullImaginaryEnergyDepth

namespace KernelEsmeralda

noncomputable section

/-- A sufficiently deep left-half zero in the square-root interior retains at
least `L²` minus the explicit compression tail. -/
theorem zeta_zero_left_half_deep_interior_finiteImaginaryEnergy_lower
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hT : 1 ≤ T)
    (hre : (rho : Complex).re ≤ 1 / 2)
    (hordL : T + Zeta23.D0 T ≤ (rho : Complex).im)
    (hordR : (rho : Complex).im ≤ 2 * T - Zeta23.D0 T)
    (hdeep :
      2 * P.L T ≤
        (P.w / 2) * Real.exp
          ((1 - 2 * (rho : Complex).re) *
            (P.L T / 2 - 3 * P.w / 2))) :
    (P.L T) ^ 2 - zetaNaturalCompressionTail P T rho ≤
      finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
  have hfull := zeta_zero_left_half_full_imaginary_energy_ge_L_sq
    P T hP hwL rho hre hdeep
  have hfinite :=
    zetaZero_finiteImaginaryEnergy_ge_full_sub_D0_tail_of_one_le_T
      P T hP hwL rho hT hordL hordR
  change
    fullImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) -
      zetaNaturalCompressionTail P T rho ≤
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) at hfinite
  linarith

end
end KernelEsmeralda
