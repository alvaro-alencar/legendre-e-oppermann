import KernelEsmeralda.ClaudeTwoThirdsBridge
import Zeta23.Statement.SeamClosed

namespace KernelEsmeralda

noncomputable section

/-- Total multiplicity in a window not lying on the critical line, expressed as
total multiplicity minus on-line multiplicity.  The Zeta23 trivial chain proves
that this real quantity is nonnegative. -/
def emeraldOffLineMultiplicityR (T₁ T₂ : Real) : Real :=
  (Zeta23.Ncount T₁ T₂ : Real) - (Zeta23.N0 T₁ T₂ : Real)

theorem emeraldOffLineMultiplicityR_nonneg (T₁ T₂ : Real) :
    0 ≤ emeraldOffLineMultiplicityR T₁ T₂ := by
  have hchain := Zeta23.trivial_chain Zeta23.zetaSeam T₁ T₂
  have hN0 : Zeta23.N0 T₁ T₂ ≤ Zeta23.Ncount T₁ T₂ := hchain.2.2.1
  have hN0R : (Zeta23.N0 T₁ T₂ : Real) ≤
      (Zeta23.Ncount T₁ T₂ : Real) := by
    exact_mod_cast hN0
  unfold emeraldOffLineMultiplicityR
  linarith

/-- The off-line multiplicity is bounded by the part of N not already certified
as simple and on the critical line. -/
theorem emeraldOffLineMultiplicityR_le_uncertified (T₁ T₂ : Real) :
    emeraldOffLineMultiplicityR T₁ T₂ ≤
      (Zeta23.Ncount T₁ T₂ : Real) -
        (Zeta23.N0simple T₁ T₂ : Real) := by
  have hchain := Zeta23.trivial_chain Zeta23.zetaSeam T₁ T₂
  have hs0star : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := hchain.1
  have hstar0 : Zeta23.N0star T₁ T₂ ≤ Zeta23.N0 T₁ T₂ := hchain.2.1
  have hs0 : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0 T₁ T₂ :=
    le_trans hs0star hstar0
  have hs0R : (Zeta23.N0simple T₁ T₂ : Real) ≤
      (Zeta23.N0 T₁ T₂ : Real) := by
    exact_mod_cast hs0
  unfold emeraldOffLineMultiplicityR
  linarith

/-- Claude's multiplicity-aware 2/3 theorem therefore gives an unconditional
asymptotic upper bound of 1/3 + epsilon for the off-critical-line multiplicity.
This is a count statement only: the explicit-formula weights can still amplify
off-line zeros according to their real parts. -/
theorem zeta23_offLine_multiplicity_le_one_third :
    ∀ ε > 0, ∃ T₀ : Real, ∀ T ≥ T₀,
      emeraldOffLineMultiplicityR T (2 * T) ≤
        (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real) := by
  intro ε hε
  obtain ⟨T₀, hrest⟩ := zeta23_uncertified_multiplicity_le_one_third ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  exact (emeraldOffLineMultiplicityR_le_uncertified T (2 * T)).trans
    (hrest T hT)

end
end KernelEsmeralda
