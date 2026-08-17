import KernelEsmeralda.ImaginaryCompressionNaturalScale

namespace KernelEsmeralda

noncomputable section

/-- In the Zeta23 operating regime `8w ≤ L` with `w ≥ 1`, the grid spacing
`h = 2π/L` is strictly below `1`. -/
theorem zeta23_hgrid_lt_one
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T) :
    P.hgrid T < 1 := by
  have hL8 : 8 ≤ P.L T := by
    have hw8 : 8 ≤ 8 * P.w := by nlinarith [hP.one_le_w]
    exact hw8.trans hwL
  have hLpos : 0 < P.L T := by linarith
  have h2pi : 2 * Real.pi < 8 := by
    nlinarith [Real.pi_lt_four]
  unfold Zeta23.Params.hgrid
  rw [div_lt_iff₀ hLpos]
  nlinarith

/-- Consequently, once `T ≥ 1`, the grid spacing is strictly below the
natural boundary margin `D₀(T)=√T`. -/
theorem zeta23_hgrid_lt_D0_of_one_le_T
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T) :
    P.hgrid T < Zeta23.D0 T := by
  have hh1 := zeta23_hgrid_lt_one P T hP hwL
  have hsqrt : 1 ≤ Real.sqrt T := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hT
  unfold Zeta23.D0
  exact hh1.trans_le hsqrt

end
end KernelEsmeralda
