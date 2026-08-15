import KernelEsmeralda.LogBarrierCriterion
import KernelEsmeralda.ResearchTarget
import KernelEsmeralda.SpectralBudget

namespace KernelEsmeralda

noncomputable section

theorem legendre_of_log_pole_budget_and_remainder
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hKle : ∀ u : Real, K u ≤ 1)
    (hsupp : Function.support K ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance K zeroSum)
    (hpole : (n : Real) ≤ (emeraldPoleTerm K).re)
    (hrem : primePowerLogBarrier n - (n : Real) <
      emeraldSpectralRemainder K zeroSum) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hre := emeraldMass_eq_spectralBalance_re K n hn hsupp zeroSum hEF
  have hmass : primePowerLogBarrier n < emeraldMass K n := by
    rw [hre]
    unfold emeraldSpectralRemainder at hrem
    change primePowerLogBarrier n - (n : Real) <
      (emeraldGammaTerm K).re - zeroSum.re at hrem
    change primePowerLogBarrier n <
      (emeraldPoleTerm K).re + (emeraldGammaTerm K).re - zeroSum.re
    linarith
  exact legendre_of_emeraldMass_gt_logBarrier K hKle n hn hmass

end
end KernelEsmeralda
