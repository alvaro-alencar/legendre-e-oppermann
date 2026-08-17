import KernelEsmeralda.ComplexPoissonConcreteEnergy
import Zeta23.Statement.SeamClosed

namespace KernelEsmeralda

noncomputable section

/-- The real coordinate of `gammaOf rho` is the ordinary zero ordinate. -/
theorem zeta23_gammaOf_re_eq_im (rho : Complex) :
    (Zeta23.gammaOf rho).re = rho.im := by
  unfold Zeta23.gammaOf
  rw [div_eq_mul_inv]
  simp [Complex.mul_re]

/-- Horizontal displacement from the critical line becomes imaginary depth in
the `gammaOf` coordinate used by Zeta23. -/
theorem zeta23_gammaOf_im_eq_half_sub_re (rho : Complex) :
    (Zeta23.gammaOf rho).im = 1 / 2 - rho.re := by
  unfold Zeta23.gammaOf
  rw [div_eq_mul_inv]
  simp [Complex.mul_im]

/-- Consequently a zero on the left half of the critical strip has
nonnegative imaginary depth in the `gammaOf` coordinate. -/
theorem zeta23_gammaOf_im_nonneg_of_re_le_half
    (rho : Complex) (hre : rho.re ≤ 1 / 2) :
    0 ≤ (Zeta23.gammaOf rho).im := by
  rw [zeta23_gammaOf_im_eq_half_sub_re]
  linarith

/-- Every point in the closed critical strip has `gammaOf` imaginary depth at
most one half in absolute value. -/
theorem zeta23_abs_gammaOf_im_le_half
    (rho : Complex) (hstrip : 0 ≤ rho.re ∧ rho.re ≤ 1) :
    |(Zeta23.gammaOf rho).im| ≤ 1 / 2 := by
  rw [zeta23_gammaOf_im_eq_half_sub_re, abs_le]
  constructor <;> linarith [hstrip.1, hstrip.2]

/-- The preceding strip bound specialized to Mathlib's nontrivial zeta zeros. -/
theorem zetaZero_abs_gammaOf_im_le_half
    (rho : Zeta23.zetaZeroConfig.carrier) :
    |(Zeta23.gammaOf (rho : Complex)).im| ≤ 1 / 2 := by
  exact zeta23_abs_gammaOf_im_le_half (rho : Complex)
    (Zeta23.zetaZeroConfig.strip (rho : Complex) rho.property)

end
end KernelEsmeralda
