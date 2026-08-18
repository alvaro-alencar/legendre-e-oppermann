import KernelEsmeralda.LinearCoreBudget

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem exists_emerald_linear_core_with_pole_budget
    (n : Nat) (hn : 1 ≤ n) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n), K x = 1) ∧
      Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n) ∧
      (n : Real) ≤ (emeraldPoleTerm K).re := by
  obtain ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport⟩ :=
    exists_emerald_minorant_linear_core n hn
  refine ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport, ?_⟩
  exact emeraldPoleTerm_re_linear_core_lower_bound K n hn
    hKsmooth.continuous hKcompact (fun u => (hKrange u).1) hKone

end
end KernelEsmeralda
