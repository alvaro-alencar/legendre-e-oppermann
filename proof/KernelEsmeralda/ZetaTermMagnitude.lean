import KernelEsmeralda.ZetaTermBound

namespace KernelEsmeralda

noncomputable section

theorem norm_exp_zero_center (n : Nat) (rho : Complex) :
    ‖Complex.exp (rho * (emeraldTaperCenter n : Complex))‖ =
      Real.exp (rho.re * emeraldTaperCenter n) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem norm_emerald_zero_kernel_factor (n : Nat) (rho : Complex) :
    ‖Complex.exp (rho * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) (-Complex.I * rho)‖ =
      Real.exp (rho.re * emeraldTaperCenter n) *
        ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) (-Complex.I * rho)‖ := by
  rw [norm_mul, norm_exp_zero_center]

theorem emerald_zero_kernel_factor_mul_sq_le
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp ((rho : Complex).re * emeraldTaperCenter n) *
        (Real.exp (emeraldTaperLength n / 2) *
          Zeta23.Taper.C1 Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)) := by
  rw [norm_emerald_zero_kernel_factor]
  have hphi := emeraldTaper_phiHat_zero_bound_strip n hn rho
  have hnonneg : 0 ≤ Real.exp ((rho : Complex).re * emeraldTaperCenter n) :=
    (Real.exp_pos _).le
  calc
    Real.exp ((rho : Complex).re * emeraldTaperCenter n) *
          ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2
        = Real.exp ((rho : Complex).re * emeraldTaperCenter n) *
          (‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2) := by ring
    _ ≤ Real.exp ((rho : Complex).re * emeraldTaperCenter n) *
          (Real.exp (emeraldTaperLength n / 2) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n)) :=
      mul_le_mul_of_nonneg_left hphi hnonneg

end
end KernelEsmeralda
