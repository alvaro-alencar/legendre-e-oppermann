import KernelEsmeralda.ClaudeWeightedOffLine
import KernelEsmeralda.ZetaDyadicCountUpper

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Claude's 2/3 theorem combined with the beta-sensitive Emerald decay and
Riemann--von Mangoldt.  The improvement appears as the multiplicative factor
1/3 + epsilon on the off-line zero count; the horizontal amplification
exp(sigma * log((n+1)^2)) remains. -/
theorem exists_claudeWeightedOffLineRvMBound
    (ε : Real) (hε : 0 < ε) :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → ∀ (sigma T : Real), T₀ ≤ T →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≠ 1 / 2 ∧
          (rho : Complex).re ≤ sigma ∧
          T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * (1 / 3 + ε) * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log T / T := by
  obtain ⟨TC, hClaude⟩ := exists_claudeWeightedOffLineDyadicBound ε hε
  obtain ⟨B, TR, hB, hRvM⟩ := exists_zeta_dyadic_count_upper
  let A : Real := Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep
  let D : Real := 8 * A * B
  let T₀ : Real := max (max TC TR) 1
  refine ⟨D, T₀, ?_, ?_⟩
  · unfold D A
    exact mul_nonneg (mul_nonneg (by norm_num) smoothstep_l1Deriv2_nonneg) hB.le
  · intro n hn sigma T hT s hs
    have hTC : TC ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
    have hTR : TR ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
    have hTone : (1 : Real) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
    have hweighted := hClaude T hTC n hn sigma s hs
    have hN := hRvM T hTR
    let C : Real :=
      (Real.exp (sigma * emeraldLogRight n) *
        (8 * A * (n : Real))) / T ^ 2
    have hC : 0 ≤ C := by
      unfold C A
      have hA := smoothstep_l1Deriv2_nonneg
      positivity
    have hfac : 0 ≤ 1 / 3 + ε := by linarith
    have hcount :
        (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real) ≤
          (1 / 3 + ε) * (B * T * Real.log T) :=
      mul_le_mul_of_nonneg_left hN hfac
    have hweighted' :
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          C * ((1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real)) := by
      simpa [C, A] using hweighted
    calc
      ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
          ≤ C * ((1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real)) := hweighted'
      _ ≤ C * ((1 / 3 + ε) * (B * T * Real.log T)) :=
        mul_le_mul_of_nonneg_left hcount hC
      _ = D * (1 / 3 + ε) * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log T / T := by
        unfold C D
        field_simp [ne_of_gt hTpos]
        ring

/-- At the natural difficult height T=n, Claude's theorem changes only the
multiplicative off-line count factor; the beta amplification survives. -/
theorem exists_claudeWeightedOffLineNaturalScaleBound
    (ε : Real) (hε : 0 < ε) :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → T₀ ≤ (n : Real) →
        ∀ (sigma : Real) (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≠ 1 / 2 ∧
          (rho : Complex).re ≤ sigma ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * (1 / 3 + ε) * Real.exp (sigma * emeraldLogRight n) *
            Real.log (n : Real) := by
  obtain ⟨D, T₀, hD, hdyadic⟩ := exists_claudeWeightedOffLineRvMBound ε hε
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT sigma s hs
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h := hdyadic n hn sigma (n : Real) hT s hs
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ D * (1 / 3 + ε) * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log (n : Real) / (n : Real) := h
    _ = D * (1 / 3 + ε) * Real.exp (sigma * emeraldLogRight n) *
          Real.log (n : Real) := by
      field_simp [hnpos.ne']

end
end KernelEsmeralda
