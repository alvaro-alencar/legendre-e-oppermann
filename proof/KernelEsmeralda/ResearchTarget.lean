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

end
end KernelEsmeralda
