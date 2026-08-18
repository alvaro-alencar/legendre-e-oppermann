import KernelEsmeralda.OffLineDyadicBeta
import KernelEsmeralda.OffLineFiniteCount

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- What Claude's multiplicity-aware 2/3 theorem buys for the Emerald explicit
sum, before any additional zero-density or cancellation input: the off-line
multiplicity factor is reduced to 1/3 + epsilon, while the beta-dependent
horizontal amplification remains untouched. -/
theorem exists_claudeWeightedOffLineDyadicBound
    (ε : Real) (hε : 0 < ε) :
    ∃ T₀ : Real, ∀ T ≥ T₀,
      ∀ (n : Nat), 1 ≤ n → ∀ (sigma : Real),
      ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
      (∀ rho ∈ s,
        (rho : Complex).re ≠ 1 / 2 ∧
        (rho : Complex).re ≤ sigma ∧
        T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) →
      ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
        ((Real.exp (sigma * emeraldLogRight n) *
          (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
            T ^ 2) *
          ((1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real)) := by
  obtain ⟨T₁, hcount⟩ := dyadic_offLine_finset_mult_real_le_one_third ε hε
  let T₀ : Real := max T₁ 1
  refine ⟨T₀, ?_⟩
  intro T hT n hn sigma s hs
  have hT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTone : (1 : Real) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hbeta : ∀ rho ∈ s,
      (rho : Complex).re ≤ sigma ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T := by
    intro rho hrho
    exact ⟨(hs rho hrho).2.1, (hs rho hrho).2.2⟩
  have hoff : ∀ rho ∈ s,
      (rho : Complex).re ≠ 1 / 2 ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T := by
    intro rho hrho
    exact ⟨(hs rho hrho).1, (hs rho hrho).2.2⟩
  have hblock := emeraldDyadicBetaBlock_bound_by_multiplicity
    n hn T hTpos sigma s hbeta
  have hcount' := hcount T hT₁ s hoff
  have hC :
      0 ≤ (Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
          T ^ 2 := by
    have hA := smoothstep_l1Deriv2_nonneg
    positivity
  exact hblock.trans (mul_le_mul_of_nonneg_left hcount' hC)

end
end KernelEsmeralda
