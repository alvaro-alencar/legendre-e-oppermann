import Zeta23.Poisson

namespace KernelEsmeralda

noncomputable section

/-- Research target suggested by the off-critical-line block geometry.

`Zeta23.Poisson` proves the sampling identity for real `τ,τ'`.  The paper also
mentions the corresponding complex continuation, but the current Lean proof
never needs it and therefore does not formalize it.

This proposition records exactly the missing extension for the concrete
Zeta23 taper family.  It is a definition, not an axiom and not a theorem. -/
def Zeta23ComplexPoissonTarget : Prop :=
  ∀ (P : Zeta23.Params) (T : Real),
    P.Valid → 8 * P.w ≤ P.L T →
    ∀ τ τ' : Complex,
      HasSum
        (fun k : Int =>
          P.phiHat T (τ - (P.tau T k : Complex)) *
            P.phiHat T (τ' - (P.tau T k : Complex)))
        ((P.L T : Complex) * P.Phi T (τ - τ'))

/-- The real slice of the complex target is already fully proved by Zeta23's
Poisson theorem.  This is the compatibility check that keeps the research
target anchored to the existing formalization. -/
theorem zeta23ComplexPoisson_real_slice
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (τ τ' : Real) :
    HasSum
      (fun k : Int =>
        P.phiHat T ((τ : Complex) - (P.tau T k : Complex)) *
          P.phiHat T ((τ' : Complex) - (P.tau T k : Complex)))
      ((P.L T : Complex) *
        P.Phi T (((τ - τ' : Real) : Complex))) := by
  have hr := Zeta23.Params.hasSum_phiHatR_mul
    (P := P) (T := T) hP hwL τ τ'
  have hc := Complex.ofRealCLM.hasSum hr
  convert hc using 1
  · funext k
    have hτ :
        (τ : Complex) - (P.tau T k : Complex) =
          (((τ - P.tau T k : Real)) : Complex) := by
      push_cast
      rfl
    have hτ' :
        (τ' : Complex) - (P.tau T k : Complex) =
          (((τ' - P.tau T k : Real)) : Complex) := by
      push_cast
      rfl
    rw [hτ, hτ', Zeta23.Params.phiHat_ofReal,
      Zeta23.Params.phiHat_ofReal]
    norm_cast
  · rw [Zeta23.Params.Phi_ofReal]
    norm_cast

/-- If the complex Poisson extension is eventually proved, its most relevant
specialization for horizontal zero depth is the conjugate pair `z, conj z`.
No positivity conclusion is asserted here; that is a separate analytic step. -/
theorem zeta23ComplexPoisson_conjugate_pair_of_target
    (hTarget : Zeta23ComplexPoissonTarget)
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        P.phiHat T (z - (P.tau T k : Complex)) *
          P.phiHat T (starRingEnd Complex z - (P.tau T k : Complex)))
      ((P.L T : Complex) *
        P.Phi T (z - starRingEnd Complex z)) := by
  exact hTarget P T hP hwL z (starRingEnd Complex z)

end
end KernelEsmeralda
