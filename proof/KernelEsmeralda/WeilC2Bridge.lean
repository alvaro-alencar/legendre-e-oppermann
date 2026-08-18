import KernelEsmeralda.Zeta23Bridge

open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem emeraldTilt_contDiff_two_of_two
    (K : Real → Real) (hK : ContDiff Real 2 K) :
    ContDiff Real 2 (emeraldTilt K) := by
  unfold emeraldTilt
  have hexp : ContDiff Real 2 (fun u : Real => Real.exp (u / 2)) := by
    fun_prop
  exact hexp.mul hK

theorem emeraldWeilTest_contDiff_two_of_two
    (K : Real → Real) (hK : ContDiff Real 2 K) :
    ContDiff Real 2 (emeraldWeilTest K) := by
  have ht := emeraldTilt_contDiff_two_of_two K hK
  change ContDiff Real 2 (fun u : Real => Complex.ofRealCLM (emeraldTilt K u))
  exact ht.continuousLinearMap_comp Complex.ofRealCLM

theorem emeraldZetaZeroSum_summable_of_two
    (K : Real → Real)
    (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : Complex) *
        Zeta23.paperFT (emeraldWeilTest K) (Zeta23.gammaOf ρ)) := by
  have hk2 := emeraldWeilTest_contDiff_two_of_two K hK
  have hkc := emeraldWeilTest_hasCompactSupport K hKcompact
  exact (zeta23_explicit_formula_available (emeraldWeilTest K) hk2 hkc).1

theorem emeraldExplicitBalance_from_zeta23_of_two
    (K : Real → Real)
    (hK : ContDiff Real 2 K)
    (hKcompact : HasCompactSupport K) :
    EmeraldExplicitBalance K (emeraldZetaZeroSum K) := by
  have hk2 := emeraldWeilTest_contDiff_two_of_two K hK
  have hkc := emeraldWeilTest_hasCompactSupport K hKcompact
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
