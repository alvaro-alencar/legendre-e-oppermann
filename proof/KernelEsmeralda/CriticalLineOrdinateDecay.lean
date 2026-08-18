import KernelEsmeralda.CriticalLineDecay

namespace KernelEsmeralda

noncomputable section

theorem emerald_zero_kernel_factor_mul_ordinate_sq_le
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * |(rho : Complex).im| ^ 2 ≤
      16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2 := by
  have him : |(rho : Complex).im| ≤ ‖(rho : Complex)‖ :=
    Complex.abs_im_le_norm (rho : Complex)
  have hsquare : |(rho : Complex).im| ^ 2 ≤ ‖(rho : Complex)‖ ^ 2 := by
    nlinarith [abs_nonneg (rho : Complex).im, norm_nonneg (rho : Complex)]
  have hmul := mul_le_mul_of_nonneg_left hsquare
    (norm_nonneg (Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
      Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex))))
  exact hmul.trans
    (emerald_zero_kernel_factor_mul_sq_le_sixteen_n_sq n hn rho hrho)

theorem emerald_zero_kernel_factor_le_div_ordinate_sq
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2)
    (hgamma : 0 < |(rho : Complex).im|) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ ≤
      (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) /
        |(rho : Complex).im| ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hgamma)]
  exact emerald_zero_kernel_factor_mul_ordinate_sq_le n hn rho hrho

end
end KernelEsmeralda
