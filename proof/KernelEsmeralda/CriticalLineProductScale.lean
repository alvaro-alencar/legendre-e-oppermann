import KernelEsmeralda.CriticalLineDyadicRvM
import KernelEsmeralda.CriticalLineBandwidthThreshold

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- At the exact bandwidth-one transition height `T = n(n+1)`, the crude
magnitude-only critical-line estimate has already fallen from the natural
`O(n log n)` scale to a logarithmic scale.  The threshold hypothesis merely
ensures the underlying explicit Riemann--von Mangoldt bound is active. -/
theorem exists_emeraldCriticalProductScaleLogBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n →
        T₀ ≤ (n : Real) * (((n + 1 : Nat) : Real)) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          (n : Real) * (((n + 1 : Nat) : Real)) < (rho : Complex).im ∧
          (rho : Complex).im ≤
            2 * ((n : Real) * (((n + 1 : Nat) : Real)))) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * Real.log ((n : Real) * (((n + 1 : Nat) : Real))) := by
  obtain ⟨D, T₀, hD, hdyadic⟩ := exists_emeraldCriticalDyadicRvMBound
  refine ⟨D, T₀, hD, ?_⟩
  intro n hn hT s hs
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  let T : Real := (n : Real) * (((n + 1 : Nat) : Real))
  have hTpos : 0 < T := by
    unfold T
    positivity
  have hTone : (1 : Real) ≤ T := by
    unfold T
    have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hsR : (1 : Real) ≤ (((n + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hTone
  have h := hdyadic n hn T hT s (by
    intro rho hrho
    simpa [T] using hs rho hrho)
  have hratio :
      (n : Real) / (((n + 1 : Nat) : Real)) ≤ 1 := by
    rw [div_le_one hspos]
    exact_mod_cast Nat.le_succ n
  have hcoef : 0 ≤ D * Real.log T := mul_nonneg hD hlog0
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ D * (n : Real) ^ 2 * Real.log T / T := h
    _ = (D * Real.log T) *
          ((n : Real) / (((n + 1 : Nat) : Real))) := by
      unfold T
      field_simp [hnpos.ne', hspos.ne']
    _ ≤ (D * Real.log T) * 1 :=
      mul_le_mul_of_nonneg_left hratio hcoef
    _ = D * Real.log ((n : Real) * (((n + 1 : Nat) : Real))) := by
      simp [T]

end
end KernelEsmeralda
