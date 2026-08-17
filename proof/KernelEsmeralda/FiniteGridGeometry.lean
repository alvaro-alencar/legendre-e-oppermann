import Zeta23.Tail

namespace KernelEsmeralda

noncomputable section

/-- The first grid point after the finite Zeta23 compression lies strictly
past `2T - h`.  This is the lower-floor companion to Zeta23's existing
`d * h ≤ T`. -/
theorem zeta23_d_succ_mul_hgrid_gt
    (P : Zeta23.Params) (T : ℝ)
    (hL : 0 < P.L T) :
    T < ((P.d T : ℝ) + 1) * P.hgrid T := by
  have hx := Nat.lt_floor_add_one (P.L T * T / (2 * Real.pi))
  change P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 at hx
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  have hm := mul_lt_mul_of_pos_right hx hh
  have heq :
      (P.L T * T / (2 * Real.pi)) * P.hgrid T = T := by
    unfold Zeta23.Params.hgrid
    field_simp
  rw [heq] at hm
  exact hm

/-- The first omitted nonnegative grid point `tau_d` lies to the right of
`2T-h`. -/
theorem zeta23_twoT_sub_hgrid_lt_tau_d
    (P : Zeta23.Params) (T : ℝ)
    (hL : 0 < P.L T) :
    2 * T - P.hgrid T < P.tau T (P.d T : ℤ) := by
  have hd := zeta23_d_succ_mul_hgrid_gt P T hL
  unfold Zeta23.Params.tau
  push_cast
  linarith

/-- The first omitted negative grid point is exactly `T-h`. -/
theorem zeta23_tau_neg_one
    (P : Zeta23.Params) (T : ℝ) :
    P.tau T (-1) = T - P.hgrid T := by
  unfold Zeta23.Params.tau
  norm_num

end
end KernelEsmeralda
