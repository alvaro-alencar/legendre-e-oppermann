import KernelEsmeralda.CriticalLineDyadicCount
import KernelEsmeralda.ZetaDyadicCountUpper

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Magnitude-only dyadic estimate for the critical-line block.  This is the
precise O(n^2 log T / T) consequence of the taper's quadratic Fourier decay
and the concrete Riemann--von Mangoldt count. -/
theorem exists_emeraldCriticalDyadicRvMBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → ∀ (T : Real), T₀ ≤ T →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * (n : Real) ^ 2 * Real.log T / T := by
  obtain ⟨B, T₁, hB, hcount⟩ := exists_zeta_dyadic_count_upper
  let A : Real := Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep
  let D : Real := 16 * A * B
  let T₀ : Real := max T₁ 1
  refine ⟨D, T₀, ?_, ?_⟩
  · unfold D A
    exact mul_nonneg (mul_nonneg (by norm_num) smoothstep_l1Deriv2_nonneg) hB.le
  · intro n hn T hT s hs
    have hT1 : T₁ ≤ T := le_trans (le_max_left _ _) hT
    have hTone : (1 : Real) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
    have hN := hcount T hT1
    have hblock := emeraldCriticalDyadicBlock_bound_by_N n hn T hTpos s hs
    have hcoef :
        0 ≤ (16 * A * (n : Real) ^ 2) / T ^ 2 := by
      unfold A
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) smoothstep_l1Deriv2_nonneg) (sq_nonneg _))
        (sq_nonneg T)
    have hmul :
        ((16 * A * (n : Real) ^ 2) / T ^ 2) *
            (Zeta23.zetaZeroConfig.N T (2 * T) : Real) ≤
          ((16 * A * (n : Real) ^ 2) / T ^ 2) *
            (B * T * Real.log T) :=
      mul_le_mul_of_nonneg_left hN hcoef
    have hblock' :
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          ((16 * A * (n : Real) ^ 2) / T ^ 2) *
            (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := by
      simpa [A] using hblock
    calc
      ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
          ≤ ((16 * A * (n : Real) ^ 2) / T ^ 2) *
              (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := hblock'
      _ ≤ ((16 * A * (n : Real) ^ 2) / T ^ 2) *
              (B * T * Real.log T) := hmul
      _ = D * (n : Real) ^ 2 * Real.log T / T := by
        unfold D
        field_simp [ne_of_gt hTpos]

end
end KernelEsmeralda
