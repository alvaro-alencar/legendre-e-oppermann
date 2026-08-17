import KernelEsmeralda.OffLineDyadicBeta
import KernelEsmeralda.CriticalLineUniformBound
import KernelEsmeralda.OffLineUnconditionalBound
import KernelEsmeralda.FullImaginaryEnergyDepth
import KernelEsmeralda.DeepInteriorFiniteEnergy

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Specializing the beta-sensitive dyadic estimate to T=n removes the explicit
factor n/T and leaves the horizontal amplification times log n. -/
theorem exists_emeraldBetaNaturalScaleBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → T₀ ≤ (n : Real) →
        ∀ (sigma : Real) (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≤ sigma ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * Real.exp (sigma * emeraldLogRight n) * Real.log (n : Real) := by
  obtain ⟨D, T₀, hD, hdyadic⟩ := exists_emeraldDyadicBetaRvMBound
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT sigma s hs
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h := hdyadic n hn sigma (n : Real) hT s hs
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ D * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log (n : Real) / (n : Real) := h
    _ = D * Real.exp (sigma * emeraldLogRight n) * Real.log (n : Real) := by
      field_simp [hnpos.ne']

/-- At beta = 1/2 the natural-scale magnitude bound is O((n+1) log n). -/
theorem exists_emeraldHalfLineNaturalScaleBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → T₀ ≤ (n : Real) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≤ 1 / 2 ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * (((n + 1 : Nat) : Real)) * Real.log (n : Real) := by
  obtain ⟨D, T₀, hD, hbeta⟩ := exists_emeraldBetaNaturalScaleBound
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT s hs
  have h := hbeta n hn hT (1 / 2) s hs
  rw [show (1 / 2 : Real) * emeraldLogRight n = emeraldLogRight n / 2 by ring,
    exp_emeraldLogRight_half_eq_succ] at h
  exact h

/-- With only the unconditional strip bound beta <= 1, the same magnitude
argument permits O((n+1)^2 log n), exposing the horizontal amplification. -/
theorem exists_emeraldStripNaturalScaleBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → T₀ ≤ (n : Real) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≤ 1 ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * upperSquare n * Real.log (n : Real) := by
  obtain ⟨D, T₀, hD, hbeta⟩ := exists_emeraldBetaNaturalScaleBound
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT s hs
  have h := hbeta n hn hT 1 s hs
  rw [one_mul, exp_emeraldLogRight_eq_upperSquare] at h
  exact h

end
end KernelEsmeralda
