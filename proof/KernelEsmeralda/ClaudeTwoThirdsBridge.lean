import Zeta23.FinalMult

namespace KernelEsmeralda

noncomputable section

/-- Direct algebraic consequence of Zeta23's multiplicity-aware Theorem B.
For every epsilon > 0 and all sufficiently large dyadic heights, the part of
the total zero multiplicity not already certified as simple and on the
critical line is at most (1/3 + epsilon) of the total multiplicity.

This remainder contains, in particular, every off-critical-line zero, but
this theorem deliberately records only the exact count consequence.  It does
not convert the count bound into a weighted explicit-formula bound. -/
theorem zeta23_uncertified_multiplicity_le_one_third :
    ∀ ε > 0, ∃ T₀ : Real, ∀ T ≥ T₀,
      (Zeta23.Ncount T (2 * T) : Real) -
          (Zeta23.N0simple T (2 * T) : Real) ≤
        (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.thmB₀_mult ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  have hB := hT₀ T hT
  linarith

end
end KernelEsmeralda
