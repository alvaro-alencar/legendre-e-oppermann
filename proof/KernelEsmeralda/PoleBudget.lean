import KernelEsmeralda.PolePositive

open Set

namespace KernelEsmeralda

noncomputable section

theorem emeraldPoleTerm_re_core_lower_bound
    (K : Real → Real) (n : Nat) (hn : 1 ≤ n)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ u : Real, 0 ≤ K u)
    (hcore : ∀ x ∈ Icc (emeraldCoreLeft n) (emeraldCoreRight n), K x = 1) :
    Real.exp (emeraldCoreRight n) - Real.exp (emeraldCoreLeft n) ≤
      (emeraldPoleTerm K).re := by
  have hneg := emeraldCore_le_global_exp_weight K n hn hKcont hKcompact hKnonneg hcore
  rw [← emeraldPaperFT_neg_pole_re K] at hneg
  have hpos := emeraldPaperFT_pos_pole_re_nonneg K hKnonneg
  unfold emeraldPoleTerm
  change Real.exp (emeraldCoreRight n) - Real.exp (emeraldCoreLeft n) ≤
    (emeraldPaperFT K (Complex.I / 2)).re +
      (emeraldPaperFT K (-Complex.I / 2)).re
  linarith

end
end KernelEsmeralda
