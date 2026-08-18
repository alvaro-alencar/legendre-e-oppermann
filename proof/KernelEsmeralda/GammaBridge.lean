import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete
import KernelEsmeralda.ZetaTarget

open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem emeraldGammaBracket_div_two_pi_eq_mu (r : Real) :
    (1 / (2 * Real.pi)) * emeraldGammaBracket r = Zeta23.mu r := by
  unfold emeraldGammaBracket Zeta23.mu
  ring

theorem emeraldGammaTerm_eq_mu_integral (K : Real → Real) :
    emeraldGammaTerm K =
      ∫ r : Real, emeraldPaperFT K r * (Zeta23.mu r : Complex) := by
  unfold emeraldGammaTerm
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  change (1 / (2 * Real.pi) : Complex) *
      (emeraldPaperFT K r * (emeraldGammaBracket r : Complex)) =
    emeraldPaperFT K r * (Zeta23.mu r : Complex)
  unfold emeraldGammaBracket Zeta23.mu
  push_cast
  ring

theorem emeraldGammaIntegrand_integrable
    (K : Real → Real)
    (hKsmooth : ContDiff Real ∞ K)
    (hKcompact : HasCompactSupport K) :
    MeasureTheory.Integrable
      (fun r : Real => emeraldPaperFT K r * (Zeta23.mu r : Complex)) := by
  have hk2 : ContDiff Real 2 (emeraldWeilTest K) :=
    emeraldWeilTest_contDiff_two K hKsmooth
  have hkc : HasCompactSupport (emeraldWeilTest K) :=
    emeraldWeilTest_hasCompactSupport K hKcompact
  simpa [emeraldPaperFT, Zeta23.paperFT] using
    Zeta23.EF.integrable_paperFT_mul_mu hk2 hkc Zeta23.gammaFacts

end
end KernelEsmeralda
