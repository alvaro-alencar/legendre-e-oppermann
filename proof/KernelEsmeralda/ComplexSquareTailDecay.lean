import KernelEsmeralda.FiniteSquareGeometry
import KernelEsmeralda.GridTailSummable
import KernelEsmeralda.GridTailRays
import KernelEsmeralda.ImaginaryEnergyTermDecay

namespace KernelEsmeralda

noncomputable section

/-- Norm of one term in the complex-square Poisson series. -/
def complexSquareNormTerm
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : ℤ) : ℝ :=
  ‖(P.phiHat T (z - (P.tau T k : ℂ))) ^ 2‖

/-- Squaring the quadratic Fourier decay gives fourth-power decay for the
norm of a complex-square summand. -/
theorem complexSquareNormTerm_mul_horizontal_weight_sq_le
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (k : ℤ) :
    complexSquareNormTerm P T z k *
        (1 + (z.re - P.tau T k) ^ 2) ^ 2 ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 := by
  let A : ℝ := ‖P.phiHat T (z - (P.tau T k : ℂ))‖
  let B : ℝ := 1 + (z.re - P.tau T k) ^ 2
  let C : ℝ := imaginaryEnergyDecayEnvelope P T z
  have hdec := zeta23_params_phiHat_complex_decay
    P T hP hwL z (P.tau T k)
  change A * B ≤ C at hdec
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hC : 0 ≤ C := hAB.trans hdec
  have hsq : (A * B) ^ 2 ≤ C ^ 2 := by
    have hdiff : 0 ≤ C - A * B := sub_nonneg.mpr hdec
    have hsum : 0 ≤ C + A * B := add_nonneg hC hAB
    nlinarith [mul_nonneg hdiff hsum]
  unfold complexSquareNormTerm
  rw [norm_pow]
  change A ^ 2 * B ^ 2 ≤ C ^ 2
  calc
    A ^ 2 * B ^ 2 = (A * B) ^ 2 := by ring
    _ ≤ C ^ 2 := hsq

/-- Reciprocal fourth-power bound once a positive horizontal distance is
available. -/
theorem complexSquareNormTerm_le_inv_four_of_distance
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (k : ℤ) (R : ℝ)
    (hR : 0 < R)
    (hdist : R ≤ |z.re - P.tau T k|) :
    complexSquareNormTerm P T z k ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 * ((R ^ 4)⁻¹) := by
  have hweighted :=
    complexSquareNormTerm_mul_horizontal_weight_sq_le P T hP hwL z k
  have hterm0 : 0 ≤ complexSquareNormTerm P T z k := norm_nonneg _
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
      complexSquareNormTerm P T z k * R ^ 4 ≤
        (imaginaryEnergyDecayEnvelope P T z) ^ 2 :=
    hmul.trans hweighted
  have hR4 : 0 < R ^ 4 := pow_pos hR 4
  change complexSquareNormTerm P T z k ≤
    (imaginaryEnergyDecayEnvelope P T z) ^ 2 / R ^ 4
  exact (le_div_iff₀ hR4).2 hbound

/-- Pointwise decay on the omitted negative grid ray. -/
theorem complexSquareNormTerm_negative_ray_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D)
    (hz : T + D ≤ z.re) (j : ℕ) :
    complexSquareNormTerm P T z (-((j : ℤ) + 1)) ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let R : ℝ := D + P.hgrid T + (j : ℝ) * P.hgrid T
  have hR : 0 < R := by
    dsimp [R]
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith [mul_nonneg hj hh.le]
  have hraw := left_omitted_grid_ray_distance P T D z.re j hz
  have hdelta : 0 ≤ z.re - P.tau T (-((j : ℤ) + 1)) := by
    dsimp [R] at hR
    linarith
  have habs :
      |z.re - P.tau T (-((j : ℤ) + 1))| =
        z.re - P.tau T (-((j : ℤ) + 1)) := abs_of_nonneg hdelta
  have hdist : R ≤ |z.re - P.tau T (-((j : ℤ) + 1))| := by
    rw [habs]
    simpa [R] using hraw
  simpa [R] using
    complexSquareNormTerm_le_inv_four_of_distance
      P T hP hwL z (-((j : ℤ) + 1)) R hR hdist

/-- Pointwise decay on the omitted right grid ray. -/
theorem complexSquareNormTerm_right_ray_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hDh : P.hgrid T < D)
    (hz : z.re ≤ 2 * T - D) (j : ℕ) :
    complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ)) ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let R : ℝ := D - P.hgrid T + (j : ℝ) * P.hgrid T
  have hR : 0 < R := by
    dsimp [R]
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith [mul_nonneg hj hh.le]
  have hraw := right_omitted_grid_ray_distance P T D z.re j hL hz
  have hdelta : z.re - P.tau T ((P.d T : ℤ) + (j : ℤ)) < 0 := by
    dsimp [R] at hR
    linarith
  have habs :
      |z.re - P.tau T ((P.d T : ℤ) + (j : ℤ))| =
        P.tau T ((P.d T : ℤ) + (j : ℤ)) - z.re := by
    rw [abs_of_neg hdelta]
    ring
  have hdist : R ≤ |z.re - P.tau T ((P.d T : ℤ) + (j : ℤ))| := by
    rw [habs]
    exact le_of_lt (by simpa [R] using hraw)
  simpa [R] using
    complexSquareNormTerm_le_inv_four_of_distance
      P T hP hwL z ((P.d T : ℤ) + (j : ℤ)) R hR hdist

/-- The negative-ray norm tail is summable and obeys the same fourth-power
integral-test bound, with coefficient one. -/
theorem summable_negative_ray_complexSquareNormTerm
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D) (hz : T + D ≤ z.re) :
    Summable (fun j : ℕ =>
      complexSquareNormTerm P T z (-((j : ℤ) + 1))) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dleft : ℝ := D + P.hgrid T
  have hDleft : 0 < Dleft := by dsimp [Dleft]; linarith
  have hmaj := (summable_inv_pow_four_grid hDleft hh).mul_left A
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmaj
  intro j
  simpa [A, Dleft] using
    complexSquareNormTerm_negative_ray_le P T D hP hwL z hD hz j

/-- The right-ray norm tail is summable. -/
theorem summable_right_ray_complexSquareNormTerm
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hDh : P.hgrid T < D) (hz : z.re ≤ 2 * T - D) :
    Summable (fun j : ℕ =>
      complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ))) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dright : ℝ := D - P.hgrid T
  have hDright : 0 < Dright := by dsimp [Dright]; linarith
  have hmaj := (summable_inv_pow_four_grid hDright hh).mul_left A
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmaj
  intro j
  simpa [A, Dright] using
    complexSquareNormTerm_right_ray_le P T D hP hwL z hDh hz j

/-- Quantitative norm bound for the negative square tail. -/
theorem negative_ray_complexSquareNorm_tsum_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D) (hz : T + D ≤ z.re) :
    (∑' j : ℕ,
      complexSquareNormTerm P T z (-((j : ℤ) + 1))) ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T) ^ 4)⁻¹ +
          ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dleft : ℝ := D + P.hgrid T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDleft : 0 < Dleft := by dsimp [Dleft]; linarith
  have hterm := summable_negative_ray_complexSquareNormTerm
    P T D hP hwL z hD hz
  have hmaj := (summable_inv_pow_four_grid hDleft hh).mul_left A
  have hle :
      (∑' j : ℕ, complexSquareNormTerm P T z (-((j : ℤ) + 1))) ≤
        ∑' j : ℕ, A * (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) :=
    hterm.tsum_le_tsum
      (fun j => by simpa [A, Dleft] using
        complexSquareNormTerm_negative_ray_le P T D hP hwL z hD hz j)
      hmaj
  calc
    (∑' j : ℕ, complexSquareNormTerm P T z (-((j : ℤ) + 1)))
        ≤ ∑' j : ℕ, A * (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := hle
    _ = A * ∑' j : ℕ, (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
      rw [← tsum_mul_left]
    _ ≤ A * ((Dleft ^ 4)⁻¹ + (Dleft ^ 3)⁻¹ / (3 * P.hgrid T)) := by
      exact mul_le_mul_of_nonneg_left (tsum_inv_pow_four_grid_le hDleft hh) hA
    _ = _ := by rfl

/-- Quantitative norm bound for the right square tail. -/
theorem right_ray_complexSquareNorm_tsum_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hDh : P.hgrid T < D) (hz : z.re ≤ 2 * T - D) :
    (∑' j : ℕ,
      complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ))) ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T) ^ 4)⁻¹ +
          ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dright : ℝ := D - P.hgrid T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDright : 0 < Dright := by dsimp [Dright]; linarith
  have hterm := summable_right_ray_complexSquareNormTerm
    P T D hP hwL z hDh hz
  have hmaj := (summable_inv_pow_four_grid hDright hh).mul_left A
  have hle :
      (∑' j : ℕ, complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ))) ≤
        ∑' j : ℕ, A * (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) :=
    hterm.tsum_le_tsum
      (fun j => by simpa [A, Dright] using
        complexSquareNormTerm_right_ray_le P T D hP hwL z hDh hz j)
      hmaj
  calc
    (∑' j : ℕ, complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ)))
        ≤ ∑' j : ℕ, A * (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := hle
    _ = A * ∑' j : ℕ, (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
      rw [← tsum_mul_left]
    _ ≤ A * ((Dright ^ 4)⁻¹ + (Dright ^ 3)⁻¹ / (3 * P.hgrid T)) := by
      exact mul_le_mul_of_nonneg_left (tsum_inv_pow_four_grid_le hDright hh) hA
    _ = _ := by rfl

end
end KernelEsmeralda
