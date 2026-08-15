import KernelEsmeralda.ZetaTermMagnitude
import Zeta23.Taper.Strip

namespace KernelEsmeralda

noncomputable section

theorem emeraldTaper_center_half_add_length_quarter (n : Nat) :
    emeraldTaperCenter n / 2 + emeraldTaperLength n / 4 =
      emeraldLogRight n / 2 := by
  unfold emeraldTaperCenter emeraldTaperLength
  ring

theorem emeraldTaper_phiHat_bound_on_critical_line
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex))‖ ≤
      Real.exp (emeraldTaperLength n / 4) * emeraldTaperLength n := by
  have h := Zeta23.Taper.norm_phiHat_le
    Zeta23.Taper.taperProfile_smoothstep
    (emeraldTaperWidth_pos n hn)
    (two_mul_emeraldTaperWidth_le_length n hn)
    (-Complex.I * (rho : Complex))
  have him : |(-Complex.I * (rho : Complex)).im| = (1 / 2 : Real) := by
    simp [hrho]
  rw [him] at h
  convert h using 1 <;> ring

theorem emerald_zero_kernel_factor_bound_on_critical_line
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ ≤
      Real.exp (emeraldLogRight n / 2) * emeraldTaperLength n := by
  rw [norm_emerald_zero_kernel_factor]
  have hphi := emeraldTaper_phiHat_bound_on_critical_line n hn rho hrho
  rw [hrho]
  have hpos : 0 ≤ Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) := by positivity
  calc
    Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) *
        ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖
      ≤ Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) *
          (Real.exp (emeraldTaperLength n / 4) * emeraldTaperLength n) :=
        mul_le_mul_of_nonneg_left hphi hpos
    _ = Real.exp (emeraldLogRight n / 2) * emeraldTaperLength n := by
      rw [show (1 / 2 : Real) * emeraldTaperCenter n = emeraldTaperCenter n / 2 by ring]
      rw [mul_assoc, ← Real.exp_add, emeraldTaper_center_half_add_length_quarter]

end
end KernelEsmeralda
