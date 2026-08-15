import KernelEsmeralda.CriticalLineWindowDecay

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

theorem norm_emeraldCriticalExplicitTerm_le_mult_dyadic
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2)
    (hheight : T < (rho : Complex).im) :
    ‖emeraldCriticalExplicitTerm n rho‖ ≤
      (Zeta23.zetaZeroConfig.mult rho : Real) *
        ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2) := by
  unfold emeraldCriticalExplicitTerm
  rw [norm_mul]
  have hmult : ‖(Zeta23.zetaZeroConfig.mult rho : Complex)‖ =
      (Zeta23.zetaZeroConfig.mult rho : Real) := by simp
  rw [hmult]
  exact mul_le_mul_of_nonneg_left
    (emerald_zero_kernel_factor_le_at_positive_height n hn T hT rho hrho hheight)
    (Nat.cast_nonneg _)

/-- Fourier-only dyadic block estimate.  No zero-counting theorem is used here. -/
theorem emeraldCriticalDyadicBlock_bound_by_multiplicity
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T)
    (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re = 1 / 2 ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
      ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2) *
        (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
  let C : Real :=
    (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2
  have hC : 0 ≤ C := by
    unfold C
    exact div_nonneg (smoothstep_decay_constant_nonneg n) (sq_nonneg T)
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ ∑ rho ∈ s, ‖emeraldCriticalExplicitTerm n rho‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real) * C := by
          apply Finset.sum_le_sum
          intro rho hrho
          simpa [C] using norm_emeraldCriticalExplicitTerm_le_mult_dyadic
            n hn T hT rho (hs rho hrho).1 (hs rho hrho).2.1
    _ = C * (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rho hrho
          ring
    _ = ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2) *
        (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by rfl

end
end KernelEsmeralda
