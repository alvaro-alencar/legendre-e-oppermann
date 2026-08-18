import KernelEsmeralda.Zeta23Bridge

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem exists_emerald_weight_reducing_legendre_to_zeta_remainder
    (n : Nat) (hn : 2 ≤ n) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n), K x = 1) ∧
      Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n) ∧
      (emeraldBarrier n - (n : Real) <
          emeraldSpectralRemainder K (emeraldZetaZeroSum K) →
        ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2) := by
  obtain ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport, hreduce⟩ :=
    exists_emerald_weight_reducing_legendre_to_remainder n hn
  refine ⟨K, hKsmooth, hKcompact, hKrange, hKone, hKsupport, ?_⟩
  intro hrem
  exact hreduce (emeraldZetaZeroSum K)
    (emeraldExplicitBalance_from_zeta23 K hKsmooth hKcompact) hrem

end
end KernelEsmeralda
