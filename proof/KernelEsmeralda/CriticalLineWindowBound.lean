import Zeta23.Tail
import KernelEsmeralda.CriticalLineDecay
import KernelEsmeralda.CriticalLineLocalCount

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The explicit multiplicity-weighted summand appearing in the Emerald zero sum. -/
def emeraldCriticalExplicitTerm (n : Nat)
    (rho : Zeta23.zetaZeroConfig.carrier) : Complex :=
  (Zeta23.zetaZeroConfig.mult rho : Complex) *
    (Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
      Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex)))

theorem norm_emeraldCriticalExplicitTerm_le_four_mult
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖emeraldCriticalExplicitTerm n rho‖ ≤
      4 * (Zeta23.zetaZeroConfig.mult rho : Real) := by
  unfold emeraldCriticalExplicitTerm
  rw [norm_mul]
  have hmult : ‖(Zeta23.zetaZeroConfig.mult rho : Complex)‖ =
      (Zeta23.zetaZeroConfig.mult rho : Real) := by simp
  rw [hmult]
  have hfactor := emerald_zero_kernel_factor_bound_four_on_critical_line n hn rho hrho
  have hm0 : 0 ≤ (Zeta23.zetaZeroConfig.mult rho : Real) := Nat.cast_nonneg _
  calc
    (Zeta23.zetaZeroConfig.mult rho : Real) *
        ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
          Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex))‖
      ≤ (Zeta23.zetaZeroConfig.mult rho : Real) * 4 :=
        mul_le_mul_of_nonneg_left hfactor hm0
    _ = 4 * (Zeta23.zetaZeroConfig.mult rho : Real) := by ring

/-- A unit-height block of critical-line zeros is controlled by the concrete
Riemann--von Mangoldt local count.  The constant A₀ is absolute and comes from
Zeta23's theorem for Mathlib's riemannZeta. -/
theorem exists_emeraldCriticalWindowBound :
    ∃ A₀ : Real, 1 ≤ A₀ ∧
      ∀ (n : Nat), 1 ≤ n → ∀ (t : Real)
        (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          t < (rho : Complex).im ∧ (rho : Complex).im ≤ t + 1) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          4 * A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    Zeta23.zetaZeroConfig hA₀ hloc
  refine ⟨A₀, hA₀, ?_⟩
  intro n hn t s hs
  have hcount :
      (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) ≤
        A₀ * Real.log (|t| + 3) := by
    exact hLC.window t s (by
      intro rho hrho
      exact (hs rho hrho).2)
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ ∑ rho ∈ s, ‖emeraldCriticalExplicitTerm n rho‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ rho ∈ s, 4 * (Zeta23.zetaZeroConfig.mult rho : Real) := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact norm_emeraldCriticalExplicitTerm_le_four_mult n hn rho (hs rho hrho).1
    _ = 4 * (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
          rw [Finset.mul_sum]
    _ ≤ 4 * (A₀ * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ = 4 * A₀ * Real.log (|t| + 3) := by ring

end
end KernelEsmeralda
