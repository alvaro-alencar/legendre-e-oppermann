import KernelEsmeralda.OffLineBetaBound

namespace KernelEsmeralda

noncomputable section

/-- The exponential of the right logarithmic endpoint is the upper square. -/
theorem exp_emeraldLogRight_eq_upperSquare
    (n : Nat) : Real.exp (emeraldLogRight n) = upperSquare n := by
  have hu : 0 < upperSquare n := by
    unfold upperSquare
    positivity
  unfold emeraldLogRight
  rw [Real.exp_log hu]

/-- Unconditional pointwise bound obtained only from the critical strip beta <= 1.
This deliberately makes no use of Claude's proportion theorem.  It records the
worst beta amplification that a magnitude-only treatment must tolerate. -/
theorem emerald_zero_kernel_factor_mul_sq_le_strip_scaled
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      upperSquare n *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real)) := by
  have hstrip := Zeta23.zetaZeroConfig.strip (rho : Complex) rho.property
  have h := emerald_zero_kernel_factor_mul_sq_le_of_re_le_scaled
    n hn rho 1 hstrip.2
  rw [one_mul, exp_emeraldLogRight_eq_upperSquare] at h
  exact h

end
end KernelEsmeralda
