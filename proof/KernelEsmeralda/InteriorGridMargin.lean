import KernelEsmeralda.FiniteGridGeometry

namespace KernelEsmeralda

noncomputable section

/-- If a real sampling ordinate lies `D` inside the left endpoint `T`, then
its distance from the first omitted negative grid point is at least `D+h`. -/
theorem left_first_omitted_grid_distance
    (P : Zeta23.Params) (T D x : ℝ)
    (hx : T + D ≤ x) :
    D + P.hgrid T ≤ x - P.tau T (-1) := by
  rw [zeta23_tau_neg_one]
  linarith

/-- If a real sampling ordinate lies `D` inside the right endpoint `2T`, then
the first omitted nonnegative grid point lies more than `D-h` to its right. -/
theorem right_first_omitted_grid_distance
    (P : Zeta23.Params) (T D x : ℝ)
    (hL : 0 < P.L T)
    (hx : x ≤ 2 * T - D) :
    D - P.hgrid T < P.tau T (P.d T : ℤ) - x := by
  have hτ := zeta23_twoT_sub_hgrid_lt_tau_d P T hL
  linarith

/-- A symmetric interior margin therefore separates a sampling ordinate from
both first omitted grid points, with the right side paying only one grid
spacing for the floor in `d = floor(T/h)`. -/
theorem interior_first_omitted_grid_distances
    (P : Zeta23.Params) (T D x : ℝ)
    (hL : 0 < P.L T)
    (hxL : T + D ≤ x)
    (hxR : x ≤ 2 * T - D) :
    D + P.hgrid T ≤ x - P.tau T (-1) ∧
      D - P.hgrid T < P.tau T (P.d T : ℤ) - x := by
  exact ⟨left_first_omitted_grid_distance P T D x hxL,
    right_first_omitted_grid_distance P T D x hL hxR⟩

end
end KernelEsmeralda
