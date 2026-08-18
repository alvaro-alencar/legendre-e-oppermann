import KernelEsmeralda.LinearCore

open Set

namespace KernelEsmeralda

noncomputable section

theorem emeraldPoleTerm_re_linear_core_lower_bound
    (K : Real → Real) (n : Nat) (hn : 1 ≤ n)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ u : Real, 0 ≤ K u)
    (hKone : ∀ x ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n), K x = 1) :
    (n : Real) ≤ (emeraldPoleTerm K).re := by
  have hchain := emeraldLinearCore_chain n hn
  have h := emeraldPoleTerm_re_interval_lower_bound K
    (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n) hchain.2.1.le
    hKcont hKcompact hKnonneg hKone
  rw [emeraldLinearCore_exp_sub n hn] at h
  exact h

end
end KernelEsmeralda
