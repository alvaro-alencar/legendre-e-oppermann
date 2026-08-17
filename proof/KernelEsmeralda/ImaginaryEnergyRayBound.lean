import KernelEsmeralda.ImaginaryEnergyTermDecay
import KernelEsmeralda.GridTailRays

namespace KernelEsmeralda

noncomputable section

/-- A quartically weighted energy bound converts to reciprocal fourth-power
decay once a positive lower bound for the horizontal distance is known. -/
theorem imaginaryEnergyTerm_le_inv_four_of_distance
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (k : ℤ) (R : ℝ)
    (hR : 0 < R)
    (hdist : R ≤ |z.re - P.tau T k|) :
    imaginaryEnergyTerm P T z k ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 * ((R ^ 4)⁻¹) := by
  have hweighted :=
    imaginaryEnergyTerm_mul_horizontal_weight_sq_le P T hP hwL z k
  have hterm0 : 0 ≤ imaginaryEnergyTerm P T z k := by
    unfold imaginaryEnergyTerm
    positivity
  have hR2 : R ^ 2 ≤ (z.re - P.tau T k) ^ 2 := by
    have hs := pow_le_pow_left₀ hR.le hdist 2
    rw [sq_abs] at hs
    exact hs
  have hbase : R ^ 2 ≤ 1 + (z.re - P.tau T k) ^ 2 := by
    nlinarith
  have hdiff :
      0 ≤ (1 + (z.re - P.tau T k) ^ 2) - R ^ 2 :=
    sub_nonneg.mpr hbase
  have hsum :
      0 ≤ (1 + (z.re - P.tau T k) ^ 2) + R ^ 2 := by
    positivity
  have hpow :
      R ^ 4 ≤ (1 + (z.re - P.tau T k) ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hdiff hsum]
  have hmul := mul_le_mul_of_nonneg_left hpow hterm0
  have hbound :
      imaginaryEnergyTerm P T z k * R ^ 4 ≤
        2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 :=
    hmul.trans hweighted
  have hR4 : 0 < R ^ 4 := pow_pos hR 4
  change imaginaryEnergyTerm P T z k ≤
    (2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2) / R ^ 4
  exact (le_div_iff₀ hR4).2 hbound

/-- Reciprocal fourth-power decay on the omitted negative grid ray for a
sampling point with left interior margin `D`. -/
theorem imaginaryEnergyTerm_negative_ray_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D)
    (hz : T + D ≤ z.re) (j : ℕ) :
    imaginaryEnergyTerm P T z (-((j : ℤ) + 1)) ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let R : ℝ := D + P.hgrid T + (j : ℝ) * P.hgrid T
  have hR : 0 < R := by
    dsimp [R]
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith [mul_nonneg hj hh.le]
  have hraw := left_omitted_grid_ray_distance P T D z.re j hz
  have hdelta :
      0 ≤ z.re - P.tau T (-((j : ℤ) + 1)) := by
    dsimp [R] at hR
    linarith
  have habs :
      |z.re - P.tau T (-((j : ℤ) + 1))| =
        z.re - P.tau T (-((j : ℤ) + 1)) := abs_of_nonneg hdelta
  have hdist :
      R ≤ |z.re - P.tau T (-((j : ℤ) + 1))| := by
    rw [habs]
    simpa [R] using hraw
  simpa [R] using
    imaginaryEnergyTerm_le_inv_four_of_distance
      P T hP hwL z (-((j : ℤ) + 1)) R hR hdist

/-- Reciprocal fourth-power decay on the omitted right grid ray for a sampling
point with right interior margin `D`, assuming one grid spacing fits inside the
margin. -/
theorem imaginaryEnergyTerm_right_ray_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hDh : P.hgrid T < D)
    (hz : z.re ≤ 2 * T - D) (j : ℕ) :
    imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ)) ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let R : ℝ := D - P.hgrid T + (j : ℝ) * P.hgrid T
  have hR : 0 < R := by
    dsimp [R]
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith [mul_nonneg hj hh.le]
  have hraw := right_omitted_grid_ray_distance P T D z.re j hL hz
  have hdelta :
      z.re - P.tau T ((P.d T : ℤ) + (j : ℤ)) < 0 := by
    dsimp [R] at hR
    linarith
  have habs :
      |z.re - P.tau T ((P.d T : ℤ) + (j : ℤ))| =
        P.tau T ((P.d T : ℤ) + (j : ℤ)) - z.re := by
    rw [abs_of_neg hdelta]
    ring
  have hdist :
      R ≤ |z.re - P.tau T ((P.d T : ℤ) + (j : ℤ))| := by
    rw [habs]
    exact le_of_lt (by simpa [R] using hraw)
  simpa [R] using
    imaginaryEnergyTerm_le_inv_four_of_distance
      P T hP hwL z ((P.d T : ℤ) + (j : ℤ)) R hR hdist

end
end KernelEsmeralda
