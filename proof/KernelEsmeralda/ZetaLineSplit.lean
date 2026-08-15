import KernelEsmeralda.WeilC2Bridge

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Nontrivial zeta zeros lying on the critical line, as a subset of the
actual Mathlib-backed zero configuration imported through Zeta23. -/
def emeraldCriticalZeros : Set Zeta23.zetaZeroConfig.carrier :=
  {rho | ((rho : Zeta23.zetaZeroConfig.carrier) : Complex).re = 1 / 2}

/-- The complementary block of nontrivial zeros, i.e. zeros off the critical line. -/
def emeraldOffCriticalZeros : Set Zeta23.zetaZeroConfig.carrier :=
  emeraldCriticalZerosᶜ

/-- One multiplicity-weighted zero-side summand for the Emerald Weil test. -/
def emeraldZetaZeroTerm (K : Real → Real)
    (rho : Zeta23.zetaZeroConfig.carrier) : Complex :=
  (Zeta23.zetaZeroConfig.mult rho : Complex) *
    Zeta23.paperFT (emeraldWeilTest K) (Zeta23.gammaOf rho)

/-- Contribution of critical-line zeros to the concrete Emerald zero sum. -/
def emeraldZetaOnLineZeroSum (K : Real → Real) : Complex :=
  ∑' rho : emeraldCriticalZeros, emeraldZetaZeroTerm K rho

/-- Contribution of off-critical-line zeros to the concrete Emerald zero sum. -/
def emeraldZetaOffLineZeroSum (K : Real → Real) : Complex :=
  ∑' rho : emeraldOffCriticalZeros, emeraldZetaZeroTerm K rho

theorem emeraldZetaZeroTerm_summable
    (K : Real → Real) (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    Summable (emeraldZetaZeroTerm K) := by
  simpa [emeraldZetaZeroTerm] using
    emeraldZetaZeroSum_summable_of_two K hK hKcompact

theorem emeraldZetaOnLineZeroSum_summable
    (K : Real → Real) (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    Summable (fun rho : emeraldCriticalZeros => emeraldZetaZeroTerm K rho) := by
  exact (emeraldZetaZeroTerm_summable K hK hKcompact).subtype emeraldCriticalZeros

theorem emeraldZetaOffLineZeroSum_summable
    (K : Real → Real) (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    Summable (fun rho : emeraldOffCriticalZeros => emeraldZetaZeroTerm K rho) := by
  exact (emeraldZetaZeroTerm_summable K hK hKcompact).subtype emeraldOffCriticalZeros

theorem emeraldZetaZeroSum_eq_onLine_add_offLine
    (K : Real → Real) (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    emeraldZetaZeroSum K =
      emeraldZetaOnLineZeroSum K + emeraldZetaOffLineZeroSum K := by
  let f : Zeta23.zetaZeroConfig.carrier → Complex := emeraldZetaZeroTerm K
  let s : Set Zeta23.zetaZeroConfig.carrier := emeraldCriticalZeros
  have hf : Summable f := by
    simpa [f] using emeraldZetaZeroTerm_summable K hK hKcompact
  have hon : Summable (f ∘ (↑) : s → Complex) := hf.subtype s
  have hoff : Summable (f ∘ (↑) : (sᶜ : Set Zeta23.zetaZeroConfig.carrier) → Complex) :=
    hf.subtype sᶜ
  have hsum : HasSum f ((∑' rho : s, f rho) + (∑' rho : sᶜ, f rho)) :=
    hon.hasSum.add_compl hoff.hasSum
  rw [← hsum.tsum_eq]
  unfold emeraldZetaZeroSum emeraldZetaOnLineZeroSum emeraldZetaOffLineZeroSum
  simp only [f, s, emeraldZetaZeroTerm, emeraldOffCriticalZeros]

end
end KernelEsmeralda
