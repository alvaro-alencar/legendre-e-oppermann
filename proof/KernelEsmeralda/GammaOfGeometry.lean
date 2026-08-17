import KernelEsmeralda.ComplexPoissonConcreteEnergy

namespace KernelEsmeralda

noncomputable section

/-- Horizontal displacement from the critical line becomes imaginary depth in
the `gammaOf` coordinate used by Zeta23. -/
theorem zeta23_gammaOf_im_eq_half_sub_re (rho : Complex) :
    (Zeta23.gammaOf rho).im = 1 / 2 - rho.re := by
  unfold Zeta23.gammaOf
  rw [div_eq_mul_inv]
  simp [Complex.mul_im]
  ring

/-- Consequently a zero on the left half of the critical strip has
nonnegative imaginary depth in the `gammaOf` coordinate. -/
theorem zeta23_gammaOf_im_nonneg_of_re_le_half
    (rho : Complex) (hre : rho.re ≤ 1 / 2) :
    0 ≤ (Zeta23.gammaOf rho).im := by
  rw [zeta23_gammaOf_im_eq_half_sub_re]
  linarith

end
end KernelEsmeralda
