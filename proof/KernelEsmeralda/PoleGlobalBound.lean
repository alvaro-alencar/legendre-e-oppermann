import KernelEsmeralda.PoleGlobal

open Set

namespace KernelEsmeralda

noncomputable section

theorem emeraldCore_le_global_exp_weight
    (K : Real → Real) (n : Nat) (hn : 1 ≤ n)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ u : Real, 0 ≤ K u)
    (hcore : ∀ x ∈ Icc (emeraldCoreLeft n) (emeraldCoreRight n), K x = 1) :
    Real.exp (emeraldCoreRight n) - Real.exp (emeraldCoreLeft n) ≤
      ∫ u : Real, Real.exp u * K u := by
  have horder : emeraldCoreLeft n ≤ emeraldCoreRight n :=
    (emeraldCoreLeft_lt_right n hn).le
  have hint : MeasureTheory.Integrable (fun u : Real => Real.exp u * K u) :=
    emeraldExpWeight_integrable K hKcont hKcompact
  have hnonneg : ∀ u : Real, 0 ≤ Real.exp u * K u := fun u =>
    mul_nonneg (Real.exp_nonneg u) (hKnonneg u)
  have hle :
      (∫ u in Ioc (emeraldCoreLeft n) (emeraldCoreRight n), Real.exp u * K u) ≤
        ∫ u : Real, Real.exp u * K u :=
    MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall hnonneg)
  have hcoreEq := emeraldCore_exp_weight_integral K n hn hcore
  rw [intervalIntegral.integral_of_le horder] at hcoreEq
  rw [hcoreEq] at hle
  exact hle

end
end KernelEsmeralda
