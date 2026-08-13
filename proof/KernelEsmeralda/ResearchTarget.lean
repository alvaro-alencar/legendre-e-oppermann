import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import KernelEsmeralda.WeilPrimeBridge

open Set MeasureTheory Complex

namespace KernelEsmeralda

noncomputable section

def emeraldBarrier (n : Nat) : Real :=
  Real.log (((n + 1 : Nat) : Real)) +
    (Real.log 4 + 4) * (upperSquare n ^ (1 / (3 : Real))) +
    (Real.log 4 + 4) * (upperSquare n ^ (1 / (5 : Real)))

def EmeraldWindowWeight (n : Nat) (K : Real → Real) : Prop :=
  (∀ u : Real, K u ≤ 1) ∧
  Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)

def emeraldPaperFT (K : Real → Real) (z : Complex) : Complex :=
  ∫ u : Real, emeraldWeilTest K u * Complex.exp (Complex.I * z * (u : Complex))

def emeraldGammaBracket (r : Real) : Real :=
  (Complex.digamma (1 / 4 + Complex.I * r / 2)).re - Real.log Real.pi

def emeraldPoleTerm (K : Real → Real) : Complex :=
  emeraldPaperFT K (Complex.I / 2) + emeraldPaperFT K (-Complex.I / 2)

def emeraldGammaTerm (K : Real → Real) : Complex :=
  (1 / (2 * Real.pi) : Complex) *
    ∫ r : Real, emeraldPaperFT K r * (emeraldGammaBracket r : Complex)

def EmeraldExplicitBalance (K : Real → Real) (zeroSum : Complex) : Prop :=
  zeroSum = emeraldPoleTerm K - emeraldWeilPrimeSide K + emeraldGammaTerm K

theorem emeraldPrimeSide_eq_spectralBalance
    (K : Real → Real) (zeroSum : Complex)
    (hEF : EmeraldExplicitBalance K zeroSum) :
    emeraldWeilPrimeSide K =
      emeraldPoleTerm K + emeraldGammaTerm K - zeroSum := by
  unfold EmeraldExplicitBalance at hEF
  rw [hEF]
  ring

theorem emeraldMass_eq_spectralBalance
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance K zeroSum) :
    (emeraldMass K n : Complex) =
      emeraldPoleTerm K + emeraldGammaTerm K - zeroSum := by
  have hside := emeraldPrimeSide_eq_spectralBalance K zeroSum hEF
  rw [emeraldWeilPrimeSide_eq_emeraldMass K n hn hsupp] at hside
  exact hside

theorem emeraldMass_eq_spectralBalance_re
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance K zeroSum) :
    emeraldMass K n =
      (emeraldPoleTerm K + emeraldGammaTerm K - zeroSum).re := by
  simpa using congrArg Complex.re
    (emeraldMass_eq_spectralBalance K n hn hsupp zeroSum hEF)

theorem legendre_of_spectralBalance_gt_barrier
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hK : ∀ u : Real, K u ≤ 1)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex)
    (hEF : EmeraldExplicitBalance K zeroSum)
    (hbound : emeraldBarrier n <
      (emeraldPoleTerm K + emeraldGammaTerm K - zeroSum).re) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hre := emeraldMass_eq_spectralBalance_re K n hn hsupp zeroSum hEF
  have hmass : emeraldBarrier n < emeraldMass K n := by
    rwa [hre]
  apply legendre_of_emeraldMass_gt_explicit_roots K hK n
  simpa [emeraldBarrier] using hmass

end
end KernelEsmeralda
