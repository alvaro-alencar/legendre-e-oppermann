import Mathlib
import Zeta23.Tail.Grid

noncomputable section

open Finset Real

namespace KernelEsmeralda

/-- Infinite-ray version of Zeta23's finite telescoping grid estimate.
For positive offset `D` and grid spacing `h`, the entire reciprocal fourth-power
ray has the same uniform upper bound as all its finite truncations. -/
theorem tsum_inv_pow_four_grid_le
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    (∑' k : ℕ, ((D + k * h) ^ 4)⁻¹) ≤
      (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  apply Real.tsum_le_of_sum_le (fun k => by positivity)
  intro s
  let N : ℕ := ∑ k ∈ s, (k + 1)
  have hsrange : s ⊆ Finset.range N := by
    intro k hk
    rw [Finset.mem_range]
    have hkterm : k + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum
        (fun j hj => Nat.zero_le (j + 1)) hk
    omega
  have hsub :
      (∑ k ∈ s, ((D + k * h) ^ 4)⁻¹) ≤
        ∑ k ∈ Finset.range N, ((D + k * h) ^ 4)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsrange
      (fun i hi hnot => by positivity)
  exact hsub.trans (Zeta23.Tail.sum_inv_pow_four_le hD hh N)

end KernelEsmeralda