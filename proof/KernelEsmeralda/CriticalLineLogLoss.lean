import KernelEsmeralda.CriticalLineDyadicRvM

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Specializing the magnitude-only dyadic estimate to the natural spectral scale T=n
leaves an O(n log n) bound.  This theorem records the logarithmic loss explicitly;
it does not assert that the true oscillatory zero sum has this size. -/
theorem exists_emeraldCriticalNaturalScaleLogBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → T₀ ≤ (n : Real) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * (n : Real) * Real.log (n : Real) := by
  obtain ⟨D, T₀, hD, hdyadic⟩ := exists_emeraldCriticalDyadicRvMBound
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT s hs
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h := hdyadic n hn (n : Real) hT s hs
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ D * (n : Real) ^ 2 * Real.log (n : Real) / (n : Real) := h
    _ = D * (n : Real) * Real.log (n : Real) := by
      field_simp [hnpos.ne']
      ring

end
end KernelEsmeralda
