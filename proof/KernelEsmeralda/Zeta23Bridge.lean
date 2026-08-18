import Zeta23.Statement.SeamClosed
import Zeta23.WeilEF.Main
import KernelEsmeralda.SpectralWitness

open scoped BigOperators ContDiff

namespace KernelEsmeralda

noncomputable section

theorem zeta23_explicit_formula_available :
    Zeta23.EF.EF_lit Zeta23.zetaZeroConfig := by
  simpa [Zeta23.zetaZeroConfig] using
    Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam

def emeraldZetaZeroSum (K : Real → Real) : Complex :=
  ∑' ρ : Zeta23.zetaZeroConfig.carrier,
    (Zeta23.zetaZeroConfig.mult ρ : Complex) *
      Zeta23.paperFT (emeraldWeilTest K) (Zeta23.gammaOf ρ)

theorem emeraldZetaZeroSum_summable
    (K : Real → Real)
    (hKsmooth : ContDiff Real ∞ K)
    (hKcompact : HasCompactSupport K) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : Complex) *
        Zeta23.paperFT (emeraldWeilTest K) (Zeta23.gammaOf ρ)) := by
  have hk2 : ContDiff Real 2 (emeraldWeilTest K) :=
    emeraldWeilTest_contDiff_two K hKsmooth
  have hkc : HasCompactSupport (emeraldWeilTest K) :=
    emeraldWeilTest_hasCompactSupport K hKcompact
  exact (zeta23_explicit_formula_available (emeraldWeilTest K) hk2 hkc).1

theorem emeraldExplicitBalance_from_zeta23
    (K : Real → Real)
    (hKsmooth : ContDiff Real ∞ K)
    (hKcompact : HasCompactSupport K) :
    EmeraldExplicitBalance K (emeraldZetaZeroSum K) := by
  have hk2 : ContDiff Real 2 (emeraldWeilTest K) :=
    emeraldWeilTest_contDiff_two K hKsmooth
  have hkc : HasCompactSupport (emeraldWeilTest K) :=
    emeraldWeilTest_hasCompactSupport K hKcompact
  have hEF := zeta23_explicit_formula_available (emeraldWeilTest K) hk2 hkc
  have heq := hEF.2
  unfold EmeraldExplicitBalance emeraldZetaZeroSum
  rw [heq]
  unfold Zeta23.EF.literatureRHS
  unfold emeraldPoleTerm emeraldGammaTerm emeraldWeilPrimeSide
  unfold emeraldPaperFT emeraldGammaBracket emeraldWeilPrimeTerm
  rfl

end
end KernelEsmeralda
