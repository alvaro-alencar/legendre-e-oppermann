import KernelEsmeralda.SpectralBudget

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem exists_emerald_weight_reducing_legendre_to_remainder
    (n : Nat) (hn : 2 ≤ n) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n), K x = 1) ∧
      Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n) ∧
      ∀ zeroSum : Complex,
        EmeraldExplicitBalance K zeroSum →
        emeraldBarrier n - (n : Real) < emeraldSpectralRemainder K zeroSum →
        ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  obtain ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport, hpole⟩ :=
    exists_emerald_linear_core_with_pole_budget n hn1
  refine ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport, ?_⟩
  intro zeroSum hEF hrem
  exact legendre_of_pole_budget_and_remainder K n hn
    (fun u => (hKrange u).2) hKsupport zeroSum hEF hpole hrem

end
end KernelEsmeralda
