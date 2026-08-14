import Zeta23.ExplicitFormula.Bridge
import KernelEsmeralda.ZetaTarget

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
  have hmu := emeraldGammaBracket_div_two_pi_eq_mu r
  change (1 / (2 * Real.pi) : Complex) *
      (emeraldPaperFT K r * (emeraldGammaBracket r : Complex)) =
    emeraldPaperFT K r * (Zeta23.mu r : Complex)
  push_cast at hmu
  rw [← hmu]
  ring

end
end KernelEsmeralda
