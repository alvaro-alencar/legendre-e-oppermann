import KernelEsmeralda.CriticalLineWindowBound
import KernelEsmeralda.CriticalLineOrdinateDecay

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

theorem smoothstep_decay_constant_nonneg (n : Nat) :
    0 ≤ 16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2 := by
  have hA := smoothstep_l1Deriv2_nonneg
  positivity

theorem emerald_zero_kernel_factor_le_at_positive_height
    (n : Nat) (hn : 1 ≤ n) (t : Real) (ht : 0 < t)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2)
    (hheight : t < (rho : Complex).im) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ ≤
      (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2 := by
  have himpos : 0 < (rho : Complex).im := lt_trans ht hheight
  have habs : |(rho : Complex).im| = (rho : Complex).im := abs_of_pos himpos
  have hgamma : 0 < |(rho : Complex).im| := by rw [habs]; exact himpos
  have hdec := emerald_zero_kernel_factor_le_div_ordinate_sq n hn rho hrho hgamma
  have htle : t ≤ |(rho : Complex).im| := by rw [habs]; exact hheight.le
  have ht2pos : 0 < t ^ 2 := sq_pos_of_pos ht
  have hsquare : t ^ 2 ≤ |(rho : Complex).im| ^ 2 := by
    nlinarith [abs_nonneg (rho : Complex).im]
  have hinv : 1 / |(rho : Complex).im| ^ 2 ≤ 1 / t ^ 2 :=
    one_div_le_one_div_of_le ht2pos hsquare
  have hC :
      0 ≤ 16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2 :=
    smoothstep_decay_constant_nonneg n
  have hratio :
      (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) /
          |(rho : Complex).im| ^ 2 ≤
        (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2 := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hC
  exact hdec.trans hratio

theorem norm_emeraldCriticalExplicitTerm_le_mult_decay
    (n : Nat) (hn : 1 ≤ n) (t : Real) (ht : 0 < t)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2)
    (hheight : t < (rho : Complex).im) :
    ‖emeraldCriticalExplicitTerm n rho‖ ≤
      (Zeta23.zetaZeroConfig.mult rho : Real) *
        ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2) := by
  unfold emeraldCriticalExplicitTerm
  rw [norm_mul]
  have hmult : ‖(Zeta23.zetaZeroConfig.mult rho : Complex)‖ =
      (Zeta23.zetaZeroConfig.mult rho : Real) := by simp
  rw [hmult]
  exact mul_le_mul_of_nonneg_left
    (emerald_zero_kernel_factor_le_at_positive_height n hn t ht rho hrho hheight)
    (Nat.cast_nonneg _)

/-- Positive unit-height windows enjoy the quadratic Fourier decay as well as the
Riemann--von Mangoldt local count. -/
theorem exists_emeraldCriticalWindowDecayBound :
    ∃ A₀ : Real, 1 ≤ A₀ ∧
      ∀ (n : Nat), 1 ≤ n → ∀ (t : Real), 0 < t →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          t < (rho : Complex).im ∧ (rho : Complex).im ≤ t + 1) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2) *
            (A₀ * Real.log (t + 3)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    Zeta23.zetaZeroConfig hA₀ hloc
  refine ⟨A₀, hA₀, ?_⟩
  intro n hn t ht s hs
  have hcount :
      (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) ≤
        A₀ * Real.log (t + 3) := by
    have h := hLC.window t s (by
      intro rho hrho
      exact (hs rho hrho).2)
    rw [abs_of_pos ht] at h
    exact h
  let C : Real :=
    (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2
  have hC : 0 ≤ C := by
    unfold C
    have hnum := smoothstep_decay_constant_nonneg n
    exact div_nonneg hnum (sq_nonneg t)
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ ∑ rho ∈ s, ‖emeraldCriticalExplicitTerm n rho‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real) * C := by
          apply Finset.sum_le_sum
          intro rho hrho
          simpa [C] using norm_emeraldCriticalExplicitTerm_le_mult_decay
            n hn t ht rho (hs rho hrho).1 (hs rho hrho).2.1
    _ = C * (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rho hrho
          ring
    _ ≤ C * (A₀ * Real.log (t + 3)) :=
          mul_le_mul_of_nonneg_left hcount hC
    _ = ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / t ^ 2) *
          (A₀ * Real.log (t + 3)) := by rfl

end
end KernelEsmeralda
