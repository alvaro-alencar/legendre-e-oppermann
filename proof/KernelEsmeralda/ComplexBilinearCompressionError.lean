import KernelEsmeralda.ComplexPoissonBilinearGeometry
import KernelEsmeralda.ComplexSquareCompressionError

namespace KernelEsmeralda

noncomputable section

/-- One bilinear sampled Poisson term. -/
def complexBilinearTerm
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) (k : ℤ) : ℂ :=
  P.phiHat T (z - (P.tau T k : ℂ)) *
    P.phiHat T (w - (P.tau T k : ℂ))

/-- Finite bilinear correlation on the actual Zeta23 compression grid. -/
def finiteComplexBilinearSum
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℂ :=
  ∑ k : Fin (P.d T),
    complexBilinearTerm P T z w (k : ℤ)

/-- The finite bilinear sum is the retained integer-grid sum. -/
theorem finiteComplexBilinearSum_eq_grid_sum
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteComplexBilinearSum P T z w =
      ∑ k ∈ finiteGridIndexSet P T, complexBilinearTerm P T z w k := by
  unfold finiteComplexBilinearSum finiteGridIndexSet
  rw [Finset.sum_map]
  rfl

/-- The full bilinear series is summable by complex Poisson. -/
theorem complexBilinearTerm_summable
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    Summable (complexBilinearTerm P T z w) := by
  have h := zeta23ComplexPoissonTarget_proved P T hP hwL z w
  simpa [complexBilinearTerm] using h.summable

/-- Exact finite-plus-tail bilinear Poisson identity. -/
theorem finiteComplexBilinearSum_add_tail_eq_poisson
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    finiteComplexBilinearSum P T z w +
        (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
          complexBilinearTerm P T z w k) =
      (P.L T : ℂ) * P.Phi T (z - w) := by
  have hsum := zeta23ComplexPoissonTarget_proved P T hP hwL z w
  have hsumm := complexBilinearTerm_summable P T hP hwL z w
  let s : Finset ℤ := finiteGridIndexSet P T
  have hsplit := hsumm.sum_add_tsum_compl (s := s)
  calc
    finiteComplexBilinearSum P T z w +
        (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
          complexBilinearTerm P T z w k)
        = (∑ k ∈ s, complexBilinearTerm P T z w k) +
            (∑' k : ↑((s : Set ℤ)ᶜ), complexBilinearTerm P T z w k) := by
              rw [finiteComplexBilinearSum_eq_grid_sum]
              rfl
    _ = ∑' k : ℤ, complexBilinearTerm P T z w k := hsplit
    _ = (P.L T : ℂ) * P.Phi T (z - w) := by
      simpa [complexBilinearTerm] using hsum.tsum_eq

/-- The bilinear compression error is the negative of the two omitted rays. -/
theorem finiteComplexBilinear_error_eq_neg_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    finiteComplexBilinearSum P T z w -
        ((P.L T : ℂ) * P.Phi T (z - w)) =
      -((∑' j : ℕ,
          complexBilinearTerm P T z w (-((j : ℤ) + 1))) +
        (∑' j : ℕ,
          complexBilinearTerm P T z w
            ((P.d T : ℤ) + (j : ℤ)))) := by
  have hfull := finiteComplexBilinearSum_add_tail_eq_poisson
    P T hP hwL z w
  have hsplit := tsum_omittedGrid_eq_two_rays_complex
    P T (complexBilinearTerm P T z w)
      (complexBilinearTerm_summable P T hP hwL z w)
  rw [hsplit] at hfull
  rw [← hfull]
  ring

/-- Pointwise arithmetic-geometric-mean majorant for one bilinear norm term. -/
theorem two_mul_norm_complexBilinearTerm_le_squareNorm_add
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) (k : ℤ) :
    2 * ‖complexBilinearTerm P T z w k‖ ≤
      complexSquareNormTerm P T z k +
        complexSquareNormTerm P T w k := by
  unfold complexBilinearTerm complexSquareNormTerm
  rw [norm_mul, norm_pow, norm_pow]
  nlinarith [sq_nonneg
    (‖P.phiHat T (z - (P.tau T k : ℂ))‖ -
      ‖P.phiHat T (w - (P.tau T k : ℂ))‖)]

/-- Summability of the bilinear norm on the omitted negative ray follows from
 the two square-norm tails. -/
theorem summable_negative_ray_complexBilinearNorm
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) (hD : 0 < D)
    (hzL : T + D ≤ z.re) (hwL' : T + D ≤ w.re) :
    Summable (fun j : ℕ =>
      ‖complexBilinearTerm P T z w (-((j : ℤ) + 1))‖) := by
  have hz := summable_negative_ray_complexSquareNormTerm
    P T D hP hwL z hD hzL
  have hw := summable_negative_ray_complexSquareNormTerm
    P T D hP hwL w hD hwL'
  have hmaj : Summable (fun j : ℕ =>
      (complexSquareNormTerm P T z (-((j : ℤ) + 1)) +
        complexSquareNormTerm P T w (-((j : ℤ) + 1))) / 2) := by
    simpa [div_eq_mul_inv, mul_add] using (hz.add hw).mul_left (1 / 2 : ℝ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmaj
  intro j
  have h := two_mul_norm_complexBilinearTerm_le_squareNorm_add
    P T z w (-((j : ℤ) + 1))
  linarith

/-- Summability of the bilinear norm on the omitted right ray. -/
theorem summable_right_ray_complexBilinearNorm
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) (hDh : P.hgrid T < D)
    (hzR : z.re ≤ 2 * T - D) (hwR : w.re ≤ 2 * T - D) :
    Summable (fun j : ℕ =>
      ‖complexBilinearTerm P T z w
        ((P.d T : ℤ) + (j : ℤ))‖) := by
  have hz := summable_right_ray_complexSquareNormTerm
    P T D hP hwL z hDh hzR
  have hw := summable_right_ray_complexSquareNormTerm
    P T D hP hwL w hDh hwR
  have hmaj : Summable (fun j : ℕ =>
      (complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ)) +
        complexSquareNormTerm P T w ((P.d T : ℤ) + (j : ℤ))) / 2) := by
    simpa [div_eq_mul_inv, mul_add] using (hz.add hw).mul_left (1 / 2 : ℝ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmaj
  intro j
  have h := two_mul_norm_complexBilinearTerm_le_squareNorm_add
    P T z w ((P.d T : ℤ) + (j : ℤ))
  linarith

/-- A compact explicit bound for the finite bilinear compression error.  It is
half the sum of the corresponding square-tail bounds for `z` and `w`. -/
theorem finiteComplexBilinear_error_norm_le_interior
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) (hD : 0 < D) (hDh : P.hgrid T < D)
    (hzL : T + D ≤ z.re) (hzR : z.re ≤ 2 * T - D)
    (hwLeft : T + D ≤ w.re) (hwRight : w.re ≤ 2 * T - D) :
    ‖finiteComplexBilinearSum P T z w -
        ((P.L T : ℂ) * P.Phi T (z - w))‖ ≤
      ((imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D + P.hgrid T) ^ 4)⁻¹ +
            ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
        (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D - P.hgrid T) ^ 4)⁻¹ +
            ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
        (imaginaryEnergyDecayEnvelope P T w) ^ 2 *
          (((D + P.hgrid T) ^ 4)⁻¹ +
            ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
        (imaginaryEnergyDecayEnvelope P T w) ^ 2 *
          (((D - P.hgrid T) ^ 4)⁻¹ +
            ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T))) / 2 := by
  rw [finiteComplexBilinear_error_eq_neg_two_rays P T hP hwL z w, norm_neg]
  let fL : ℕ → ℂ := fun j =>
    complexBilinearTerm P T z w (-((j : ℤ) + 1))
  let fR : ℕ → ℂ := fun j =>
    complexBilinearTerm P T z w ((P.d T : ℤ) + (j : ℤ))
  have hnormL := summable_negative_ray_complexBilinearNorm
    P T D hP hwL z w hD hzL hwLeft
  have hnormR := summable_right_ray_complexBilinearNorm
    P T D hP hwL z w hDh hzR hwRight
  have htri := norm_add_le (∑' j, fL j) (∑' j, fR j)
  have hLnorm := norm_tsum_le_tsum_norm (by simpa [fL] using hnormL)
  have hRnorm := norm_tsum_le_tsum_norm (by simpa [fR] using hnormR)
  have hzLtail := negative_ray_complexSquareNorm_tsum_le
    P T D hP hwL z hD hzL
  have hzRtail := right_ray_complexSquareNorm_tsum_le
    P T D hP hwL z hDh hzR
  have hwLtail := negative_ray_complexSquareNorm_tsum_le
    P T D hP hwL w hD hwLeft
  have hwRtail := right_ray_complexSquareNorm_tsum_le
    P T D hP hwL w hDh hwRight
  have hleftTerm :
      (∑' j : ℕ, ‖fL j‖) ≤
        ((∑' j : ℕ,
          complexSquareNormTerm P T z (-((j : ℤ) + 1))) +
         (∑' j : ℕ,
          complexSquareNormTerm P T w (-((j : ℤ) + 1)))) / 2 := by
    have hmaj : Summable (fun j : ℕ =>
        (complexSquareNormTerm P T z (-((j : ℤ) + 1)) +
          complexSquareNormTerm P T w (-((j : ℤ) + 1))) / 2) := by
      have hz := summable_negative_ray_complexSquareNormTerm
        P T D hP hwL z hD hzL
      have hw := summable_negative_ray_complexSquareNormTerm
        P T D hP hwL w hD hwLeft
      simpa [div_eq_mul_inv, mul_add] using (hz.add hw).mul_left (1 / 2 : ℝ)
    exact (by simpa [fL] using hnormL).tsum_le_tsum
      (fun j => by
        have h := two_mul_norm_complexBilinearTerm_le_squareNorm_add
          P T z w (-((j : ℤ) + 1))
        linarith)
      hmaj
  have hrightTerm :
      (∑' j : ℕ, ‖fR j‖) ≤
        ((∑' j : ℕ,
          complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ))) +
         (∑' j : ℕ,
          complexSquareNormTerm P T w ((P.d T : ℤ) + (j : ℤ)))) / 2 := by
    have hmaj : Summable (fun j : ℕ =>
        (complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ)) +
          complexSquareNormTerm P T w ((P.d T : ℤ) + (j : ℤ))) / 2) := by
      have hz := summable_right_ray_complexSquareNormTerm
        P T D hP hwL z hDh hzR
      have hw := summable_right_ray_complexSquareNormTerm
        P T D hP hwL w hDh hwRight
      simpa [div_eq_mul_inv, mul_add] using (hz.add hw).mul_left (1 / 2 : ℝ)
    exact (by simpa [fR] using hnormR).tsum_le_tsum
      (fun j => by
        have h := two_mul_norm_complexBilinearTerm_le_squareNorm_add
          P T z w ((P.d T : ℤ) + (j : ℤ))
        linarith)
      hmaj
  change ‖(∑' j, fL j) + (∑' j, fR j)‖ ≤ _
  calc
    ‖(∑' j, fL j) + (∑' j, fR j)‖
        ≤ ‖∑' j, fL j‖ + ‖∑' j, fR j‖ := htri
    _ ≤ (∑' j, ‖fL j‖) + (∑' j, ‖fR j‖) :=
      add_le_add hLnorm hRnorm
    _ ≤ (((∑' j : ℕ,
          complexSquareNormTerm P T z (-((j : ℤ) + 1))) +
         (∑' j : ℕ,
          complexSquareNormTerm P T w (-((j : ℤ) + 1)))) / 2) +
        (((∑' j : ℕ,
          complexSquareNormTerm P T z ((P.d T : ℤ) + (j : ℤ))) +
         (∑' j : ℕ,
          complexSquareNormTerm P T w ((P.d T : ℤ) + (j : ℤ)))) / 2) :=
      add_le_add hleftTerm hrightTerm
    _ ≤ _ := by
      linarith [hzLtail, hzRtail, hwLtail, hwRtail]

end
end KernelEsmeralda
