import KernelEsmeralda.ZetaTermMagnitude

namespace KernelEsmeralda

noncomputable section

theorem critical_zero_eq_half_add_I_im
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    (rho : Complex) = (1 / 2 : Complex) + Complex.I * ((rho : Complex).im : Complex) := by
  apply Complex.ext
  · simp [hrho]
  · simp

theorem neg_I_mul_critical_zero
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    -Complex.I * (rho : Complex) =
      ((rho : Complex).im : Complex) - Complex.I / 2 := by
  calc
    -Complex.I * (rho : Complex)
        = -Complex.I *
            ((1 / 2 : Complex) + Complex.I * ((rho : Complex).im : Complex)) := by
              rw [critical_zero_eq_half_add_I_im rho hrho]
    _ = -Complex.I / 2 -
          (Complex.I * Complex.I) * ((rho : Complex).im : Complex) := by ring
    _ = ((rho : Complex).im : Complex) - Complex.I / 2 := by
          rw [Complex.I_mul_I]
          ring

theorem exp_critical_zero_center_factorization
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) =
      Complex.exp ((emeraldTaperCenter n / 2 : Real) : Complex) *
        Complex.exp
          (Complex.I * ((rho : Complex).im : Complex) *
            (emeraldTaperCenter n : Complex)) := by
  have harg :
      ((1 / 2 : Complex) + Complex.I * ((rho : Complex).im : Complex)) *
          (emeraldTaperCenter n : Complex) =
        ((emeraldTaperCenter n / 2 : Real) : Complex) +
          Complex.I * ((rho : Complex).im : Complex) *
            (emeraldTaperCenter n : Complex) := by
    push_cast
    ring
  calc
    Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex))
        = Complex.exp
            (((1 / 2 : Complex) + Complex.I * ((rho : Complex).im : Complex)) *
              (emeraldTaperCenter n : Complex)) := by
                rw [critical_zero_eq_half_add_I_im rho hrho]
    _ = Complex.exp
          (((emeraldTaperCenter n / 2 : Real) : Complex) +
            Complex.I * ((rho : Complex).im : Complex) *
              (emeraldTaperCenter n : Complex)) := by rw [harg]
    _ = Complex.exp ((emeraldTaperCenter n / 2 : Real) : Complex) *
          Complex.exp
            (Complex.I * ((rho : Complex).im : Complex) *
              (emeraldTaperCenter n : Complex)) := by
                rw [Complex.exp_add]

/-- Exact oscillatory form of the taper factor at a critical-line zero. -/
theorem emerald_zero_kernel_factor_phase_form
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex)) =
      Complex.exp ((emeraldTaperCenter n / 2 : Real) : Complex) *
        Complex.exp
          (Complex.I * ((rho : Complex).im : Complex) *
            (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (((rho : Complex).im : Complex) - Complex.I / 2) := by
  rw [exp_critical_zero_center_factorization n rho hrho,
    neg_I_mul_critical_zero rho hrho]

end
end KernelEsmeralda
