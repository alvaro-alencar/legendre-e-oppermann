import KernelEsmeralda.ResearchTarget

namespace KernelEsmeralda

noncomputable section

theorem emeraldPolePos_integrand
    (K : Real → Real) (u : Real) :
    emeraldWeilTest K u *
        Complex.exp (Complex.I * (Complex.I / 2) * (u : Complex)) =
      (K u : Complex) := by
  have harg :
      Complex.I * (Complex.I / 2) * (u : Complex) =
        ((-u / 2 : Real) : Complex) := by
    rw [Complex.I_mul_I]
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  change
    ((Real.exp (u / 2) * K u : Real) : Complex) *
        (Real.exp (-u / 2) : Complex) = (K u : Complex)
  norm_cast
  calc
    Real.exp (u / 2) * K u * Real.exp (-u / 2) =
        (Real.exp (u / 2) * Real.exp (-u / 2)) * K u := by ring
    _ = K u := by
      rw [← Real.exp_add]
      ring_nf
      simp

theorem emeraldPoleNeg_integrand
    (K : Real → Real) (u : Real) :
    emeraldWeilTest K u *
        Complex.exp (Complex.I * (-Complex.I / 2) * (u : Complex)) =
      ((Real.exp u * K u : Real) : Complex) := by
  have harg :
      Complex.I * (-Complex.I / 2) * (u : Complex) =
        ((u / 2 : Real) : Complex) := by
    rw [mul_div_assoc, Complex.I_mul_neg_I]
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  change
    ((Real.exp (u / 2) * K u : Real) : Complex) *
        (Real.exp (u / 2) : Complex) =
      ((Real.exp u * K u : Real) : Complex)
  norm_cast
  calc
    Real.exp (u / 2) * K u * Real.exp (u / 2) =
        (Real.exp (u / 2) * Real.exp (u / 2)) * K u := by ring
    _ = Real.exp u * K u := by
      rw [← Real.exp_add]
      ring_nf

end
end KernelEsmeralda
