import KernelEsmeralda.CriticalLineDecay
import KernelEsmeralda.ZetaTermMagnitude

namespace KernelEsmeralda

noncomputable section

/-- The translation center plus half the taper length is exactly the right
edge of the logarithmic Legendre window. -/
theorem emeraldTaper_center_add_length_half (n : Nat) :
    emeraldTaperCenter n + emeraldTaperLength n / 2 = emeraldLogRight n := by
  unfold emeraldTaperCenter emeraldTaperLength
  ring

/-- Exact pointwise beta-sensitive bound for the Emerald taper at any actual
nontrivial zeta zero.  The exponential amplification depends on beta = Re rho
and reaches the right edge of the Legendre logarithmic window. -/
theorem emerald_zero_kernel_factor_mul_sq_le_beta_right
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp ((rho : Complex).re * emeraldLogRight n) *
        Zeta23.Taper.C1 Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) := by
  rw [norm_emerald_zero_kernel_factor]
  have hphi := emeraldTaper_phiHat_zero_bound_raw n hn rho
  have hstrip := Zeta23.zetaZeroConfig.strip (rho : Complex) rho.property
  have hreabs : |(rho : Complex).re| = (rho : Complex).re :=
    abs_of_nonneg hstrip.1
  rw [hreabs] at hphi
  have hcenter : 0 ≤ Real.exp ((rho : Complex).re * emeraldTaperCenter n) :=
    Real.exp_nonneg _
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
          (Real.exp ((rho : Complex).re * (emeraldTaperLength n / 2)) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n)) :=
        mul_le_mul_of_nonneg_left hphi hcenter
    _ = (Real.exp ((rho : Complex).re * emeraldTaperCenter n) *
          Real.exp ((rho : Complex).re * (emeraldTaperLength n / 2))) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n) := by ring
    _ = Real.exp
          ((rho : Complex).re * emeraldTaperCenter n +
            (rho : Complex).re * (emeraldTaperLength n / 2)) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n) := by
          rw [Real.exp_add]
    _ = Real.exp ((rho : Complex).re * emeraldLogRight n) *
          Zeta23.Taper.C1 Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n) := by
          congr 1
          rw [← mul_add, emeraldTaper_center_add_length_half]

/-- The right endpoint logarithm is nonnegative for every n. -/
theorem emeraldLogRight_nonneg (n : Nat) : 0 ≤ emeraldLogRight n := by
  have hs : (1 : Real) ≤ (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hu : (1 : Real) ≤ upperSquare n := by
    unfold upperSquare
    nlinarith [sq_nonneg ((((n + 1 : Nat) : Real)) - 1)]
  unfold emeraldLogRight
  exact Real.log_nonneg hu

/-- If beta is known to lie below sigma, the zero term is bounded by the same
right-edge exponential evaluated at sigma.  This isolates exactly what a
zero-density or zero-free input would need to control. -/
theorem emerald_zero_kernel_factor_mul_sq_le_of_re_le
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (sigma : Real) (hre : (rho : Complex).re ≤ sigma) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp (sigma * emeraldLogRight n) *
        Zeta23.Taper.C1 Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) := by
  have hbase := emerald_zero_kernel_factor_mul_sq_le_beta_right n hn rho
  have hlog0 := emeraldLogRight_nonneg n
  have hexp :
      Real.exp ((rho : Complex).re * emeraldLogRight n) ≤
        Real.exp (sigma * emeraldLogRight n) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hre hlog0
  have hC : 0 ≤ Zeta23.Taper.C1 Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n) := by
    unfold Zeta23.Taper.C1
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  exact hbase.trans (mul_le_mul_of_nonneg_right hexp hC)

/-- Combining the beta-sensitive exponential with the explicit taper derivative
cost gives a fully concrete n-dependent pointwise bound. -/
theorem emerald_zero_kernel_factor_mul_sq_le_of_re_le_scaled
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (sigma : Real) (hre : (rho : Complex).re ≤ sigma) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real)) := by
  have hbase := emerald_zero_kernel_factor_mul_sq_le_of_re_le n hn rho sigma hre
  have hC := emeraldTaper_C1_le_eight_mul_n n hn
  have hexp0 : 0 ≤ Real.exp (sigma * emeraldLogRight n) := Real.exp_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_left hC hexp0)

end
end KernelEsmeralda
