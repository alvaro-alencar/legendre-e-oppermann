import KernelEsmeralda.ComplexPoissonCrossEnergy
import KernelEsmeralda.FiniteImaginaryEnergy

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The finite complex square sum sampled by the same Zeta23 compression. -/
def finiteComplexSquareSum
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin (P.d T),
    (P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))) ^ 2

/-- Twice the finite real-part energy.  The factor two matches the existing
`finiteImaginaryEnergy`. -/
def finiteRealEnergy
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))).re ^ 2

/-- The finite real-imaginary cross energy. -/
def finiteCrossEnergy
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))).re *
      (P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))).im

theorem complex_sq_re_eq_re_sq_sub_im_sq (w : ℂ) :
    (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
  simp [pow_two, Complex.mul_re]
  ring

/-- The imaginary part of the finite complex square sum is exactly the finite
cross energy. -/
theorem finiteComplexSquareSum_im
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    (finiteComplexSquareSum P T z).im = finiteCrossEnergy P T z := by
  unfold finiteComplexSquareSum finiteCrossEnergy
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact complex_sq_im_eq_two_re_mul_im _

/-- The real part of the finite complex square sum records half the difference
between real and imaginary finite energies. -/
theorem two_mul_finiteComplexSquareSum_re
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    2 * (finiteComplexSquareSum P T z).re =
      finiteRealEnergy P T z - finiteImaginaryEnergy P T z := by
  unfold finiteComplexSquareSum finiteRealEnergy finiteImaginaryEnergy
  rw [map_sum, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [complex_sq_re_eq_re_sq_sub_im_sq]
  ring

/-- A norm bound on the finite complex-square error immediately controls the
loss of real-imaginary orthogonality. -/
theorem abs_finiteCrossEnergy_le_of_square_error
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) {ε : ℝ}
    (herr : ‖finiteComplexSquareSum P T z -
      ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ ≤ ε) :
    |finiteCrossEnergy P T z| ≤ ε := by
  have him :
      |(finiteComplexSquareSum P T z -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ)).im| ≤
        ‖finiteComplexSquareSum P T z -
          ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ :=
    Complex.abs_im_le_norm _
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero,
    finiteComplexSquareSum_im] at him
  exact him.trans herr

/-- The same complex-square error controls the finite real-minus-imaginary
energy identity. -/
theorem abs_real_sub_imag_sub_baseline_le_of_square_error
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) {ε : ℝ}
    (herr : ‖finiteComplexSquareSum P T z -
      ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ ≤ ε) :
    |finiteRealEnergy P T z - finiteImaginaryEnergy P T z -
        2 * (P.a T * P.L T ^ 2)| ≤ 2 * ε := by
  have hre :
      |(finiteComplexSquareSum P T z -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ)).re| ≤
        ‖finiteComplexSquareSum P T z -
          ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have hre' := hre.trans herr
  rw [← two_mul_finiteComplexSquareSum_re P T z]
  have htwo : 0 ≤ (2 : ℝ) := by norm_num
  have := mul_le_mul_of_nonneg_left hre' htwo
  rw [← abs_mul] at this
  convert this using 1 <;> ring

end
end KernelEsmeralda
