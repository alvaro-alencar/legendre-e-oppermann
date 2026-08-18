import KernelEsmeralda.InteriorGridMargin

namespace KernelEsmeralda

noncomputable section

/-- The omitted negative grid ray, indexed from its first point `-1`. -/
theorem zeta23_tau_negative_ray
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    P.tau T (-((j : ℤ) + 1)) =
      P.tau T (-1) - (j : ℝ) * P.hgrid T := by
  unfold Zeta23.Params.tau
  push_cast
  ring

/-- The omitted nonnegative grid ray, indexed from its first point `d`. -/
theorem zeta23_tau_right_ray
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    P.tau T ((P.d T : ℤ) + (j : ℤ)) =
      P.tau T (P.d T : ℤ) + (j : ℝ) * P.hgrid T := by
  unfold Zeta23.Params.tau
  push_cast
  ring

/-- An interior point stays at least `D+h+jh` from the `j`th omitted point on
the negative grid ray. -/
theorem left_omitted_grid_ray_distance
    (P : Zeta23.Params) (T D x : ℝ) (j : ℕ)
    (hx : T + D ≤ x) :
    D + P.hgrid T + (j : ℝ) * P.hgrid T ≤
      x - P.tau T (-((j : ℤ) + 1)) := by
  have h0 := left_first_omitted_grid_distance P T D x hx
  rw [zeta23_tau_negative_ray P T j]
  linarith

/-- An interior point stays more than `D-h+jh` from the `j`th omitted point
on the right grid ray. -/
theorem right_omitted_grid_ray_distance
    (P : Zeta23.Params) (T D x : ℝ) (j : ℕ)
    (hL : 0 < P.L T)
    (hx : x ≤ 2 * T - D) :
    D - P.hgrid T + (j : ℝ) * P.hgrid T <
      P.tau T ((P.d T : ℤ) + (j : ℤ)) - x := by
  have h0 := right_first_omitted_grid_distance P T D x hL hx
  rw [zeta23_tau_right_ray P T j]
  linarith

end
end KernelEsmeralda
