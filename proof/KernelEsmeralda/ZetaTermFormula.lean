import KernelEsmeralda.EmeraldTaperFourier
import KernelEsmeralda.Zeta23Bridge

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

theorem gammaOf_sub_half_I (rho : Complex) :
    Zeta23.gammaOf rho - Complex.I / 2 = -Complex.I * rho := by
  unfold Zeta23.gammaOf
  field_simp [Complex.I_ne_zero]
  simp [pow_two, Complex.I_mul_I]

theorem I_mul_gammaOf_sub_half_I (rho : Complex) :
    Complex.I * (Zeta23.gammaOf rho - Complex.I / 2) = rho := by
  rw [gammaOf_sub_half_I]
  calc
    Complex.I * (-Complex.I * rho) = -(Complex.I * Complex.I) * rho := by ring
    _ = rho := by rw [Complex.I_mul_I]; ring

theorem emeraldTaper_zero_term_formula (n : Nat) (rho : Complex) :
    emeraldPaperFT (emeraldTaperWeight n) (Zeta23.gammaOf rho) =
      Complex.exp (rho * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) (-Complex.I * rho) := by
  rw [emeraldTaper_paperFT_formula]
  rw [gammaOf_sub_half_I]
  have hexp :
      Complex.I * (-Complex.I * rho) * (emeraldTaperCenter n : Complex) =
        rho * (emeraldTaperCenter n : Complex) := by
    calc
      Complex.I * (-Complex.I * rho) * (emeraldTaperCenter n : Complex)
          = (-(Complex.I * Complex.I) * rho) * (emeraldTaperCenter n : Complex) := by ring
      _ = rho * (emeraldTaperCenter n : Complex) := by
        rw [Complex.I_mul_I]
        ring
  rw [hexp]

theorem emeraldZetaZeroSum_explicit_taper (n : Nat) :
    emeraldZetaZeroSum (emeraldTaperWeight n) =
      ∑' rho : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
          Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex)) := by
  unfold emeraldZetaZeroSum
  apply tsum_congr
  intro rho
  change
    (Zeta23.zetaZeroConfig.mult rho : Complex) *
      emeraldPaperFT (emeraldTaperWeight n) (Zeta23.gammaOf (rho : Complex)) = _
  rw [emeraldTaper_zero_term_formula]
  ring

end
end KernelEsmeralda
