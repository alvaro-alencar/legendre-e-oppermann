import KernelEsmeralda.GridTailInfinite

namespace KernelEsmeralda

noncomputable section

/-- The reciprocal fourth-power grid ray is summable for positive offset and
positive spacing.  This is the summability companion to
`tsum_inv_pow_four_grid_le`. -/
theorem summable_inv_pow_four_grid
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    Summable (fun k : ℕ => ((D + k * h) ^ 4)⁻¹) := by
  refine summable_of_sum_le
    (c := (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h))
    (fun k => by positivity) ?_
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

end
end KernelEsmeralda
