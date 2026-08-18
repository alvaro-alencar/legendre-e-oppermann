import KernelEsmeralda.LinearCoreWitness

namespace KernelEsmeralda

noncomputable section

def emeraldSpectralRemainder (K : Real → Real) (zeroSum : Complex) : Real :=
  (emeraldGammaTerm K - zeroSum).re

theorem legendre_of_pole_budget_and_remainder
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hKle : ∀ u : Real, K u ≤ 1)
    (hsupp : Function.support K ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance K zeroSum)
    (hpole : (n : Real) ≤ (emeraldPoleTerm K).re)
    (hrem : emeraldBarrier n - (n : Real) < emeraldSpectralRemainder K zeroSum) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hbound : emeraldBarrier n <
      (emeraldPoleTerm K + emeraldGammaTerm K - zeroSum).re := by
    unfold emeraldSpectralRemainder at hrem
    change emeraldBarrier n - (n : Real) <
      (emeraldGammaTerm K).re - zeroSum.re at hrem
    change emeraldBarrier n <
      (emeraldPoleTerm K).re + (emeraldGammaTerm K).re - zeroSum.re
    linarith
  exact legendre_of_spectralBalance_gt_barrier K n hn hKle hsupp zeroSum hEF hbound

end
end KernelEsmeralda
