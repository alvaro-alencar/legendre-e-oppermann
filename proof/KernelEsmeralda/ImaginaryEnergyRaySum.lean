import KernelEsmeralda.ImaginaryEnergyRayBound
import KernelEsmeralda.GridTailInfinite

namespace KernelEsmeralda

noncomputable section

/-- The entire omitted negative ray has an explicit fourth-power tail bound
for a sampling point with left interior margin `D`. -/
theorem negative_ray_imaginary_energy_tsum_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D)
    (hz : T + D ≤ z.re) :
    (∑' j : ℕ, imaginaryEnergyTerm P T z (-((j : ℤ) + 1))) ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T) ^ 4)⁻¹ +
          ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := 2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dleft : ℝ := D + P.hgrid T
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hDleft : 0 < Dleft := by
    dsimp [Dleft]
    linarith
  apply Real.tsum_le_of_sum_le
    (fun j => by unfold imaginaryEnergyTerm; positivity)
  intro s
  let N : ℕ := ∑ j ∈ s, (j + 1)
  have hsrange : s ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    have hjterm : j + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum
        (fun i hi => Nat.zero_le (i + 1)) hj
    omega
  calc
    (∑ j ∈ s, imaginaryEnergyTerm P T z (-((j : ℤ) + 1)))
        ≤ ∑ j ∈ s,
            A * (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [A, Dleft] using
            imaginaryEnergyTerm_negative_ray_le P T D hP hwL z hD hz j
    _ = A * ∑ j ∈ s,
          (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ A * ∑ j ∈ Finset.range N,
          (((Dleft + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact Finset.sum_le_sum_of_subset_of_nonneg hsrange
            (fun i hi hnot => by positivity)
    _ ≤ A *
          ((Dleft ^ 4)⁻¹ + (Dleft ^ 3)⁻¹ / (3 * P.hgrid T)) := by
          exact mul_le_mul_of_nonneg_left
            (Zeta23.Tail.sum_inv_pow_four_le hDleft hh N) hA
    _ = 2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D + P.hgrid T) ^ 4)⁻¹ +
            ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
          rfl

/-- The entire omitted right ray has an explicit fourth-power tail bound for a
sampling point with right interior margin `D`. -/
theorem right_ray_imaginary_energy_tsum_le
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hDh : P.hgrid T < D)
    (hz : z.re ≤ 2 * T - D) :
    (∑' j : ℕ,
        imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ))) ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T) ^ 4)⁻¹ +
          ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hh : 0 < P.hgrid T := by
    unfold Zeta23.Params.hgrid
    positivity
  let A : ℝ := 2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2
  let Dright : ℝ := D - P.hgrid T
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hDright : 0 < Dright := by
    dsimp [Dright]
    linarith
  apply Real.tsum_le_of_sum_le
    (fun j => by unfold imaginaryEnergyTerm; positivity)
  intro s
  let N : ℕ := ∑ j ∈ s, (j + 1)
  have hsrange : s ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    have hjterm : j + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum
        (fun i hi => Nat.zero_le (i + 1)) hj
    omega
  calc
    (∑ j ∈ s,
        imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ)))
        ≤ ∑ j ∈ s,
            A * (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          apply Finset.sum_le_sum
          intro j hj
          simpa [A, Dright] using
            imaginaryEnergyTerm_right_ray_le P T D hP hwL z hDh hz j
    _ = A * ∑ j ∈ s,
          (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ A * ∑ j ∈ Finset.range N,
          (((Dright + (j : ℝ) * P.hgrid T) ^ 4)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact Finset.sum_le_sum_of_subset_of_nonneg hsrange
            (fun i hi hnot => by positivity)
    _ ≤ A *
          ((Dright ^ 4)⁻¹ + (Dright ^ 3)⁻¹ / (3 * P.hgrid T)) := by
          exact mul_le_mul_of_nonneg_left
            (Zeta23.Tail.sum_inv_pow_four_le hDright hh N) hA
    _ = 2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D - P.hgrid T) ^ 4)⁻¹ +
            ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
          rfl

end
end KernelEsmeralda
