import KernelEsmeralda.ZetaTermFormula
import Zeta23.Taper.Strip

namespace KernelEsmeralda

noncomputable section

theorem emeraldTaper_phiHat_zero_bound_raw
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier) :
    ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp (|(rho : Complex).re| * (emeraldTaperLength n / 2)) *
        Zeta23.Taper.C1 Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) := by
  have h := Zeta23.Taper.norm_phiHat_mul_sq_le
    Zeta23.Taper.taperProfile_smoothstep
    (emeraldTaperWidth_pos n hn)
    (two_mul_emeraldTaperWidth_le_length n hn)
    (-Complex.I * (rho : Complex))
  simpa [norm_mul] using h

theorem emeraldTaper_phiHat_zero_bound_strip
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier) :
    ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp (emeraldTaperLength n / 2) *
        Zeta23.Taper.C1 Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) := by
  have hraw := emeraldTaper_phiHat_zero_bound_raw n hn rho
  have hstrip := Zeta23.zetaZeroConfig.strip (rho : Complex) rho.property
  have hL : 0 ≤ emeraldTaperLength n := by
    have hc := emeraldLinearCore_chain n hn
    unfold emeraldTaperLength
    linarith
  have hre : |(rho : Complex).re| = (rho : Complex).re := abs_of_nonneg hstrip.1
  rw [hre] at hraw
  have hexp :
      Real.exp ((rho : Complex).re * (emeraldTaperLength n / 2)) ≤
        Real.exp (emeraldTaperLength n / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hstrip.2]
  have hC : 0 ≤ Zeta23.Taper.C1 Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n) := by
    unfold Zeta23.Taper.C1
    exact MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  exact hraw.trans (mul_le_mul_of_nonneg_right hexp hC)

end
end KernelEsmeralda
