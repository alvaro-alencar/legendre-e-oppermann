import Zeta23.Poisson.PaperFT

open Complex MeasureTheory

namespace KernelEsmeralda

noncomputable section

theorem paperFT_translate
    (f : Real → Complex) (c : Real) (z : Complex) :
    Zeta23.paperFT (fun u : Real => f (u - c)) z =
      Complex.exp (Complex.I * z * (c : Complex)) * Zeta23.paperFT f z := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def]
  rw [← integral_add_right_eq_self _ c]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  have harg :
      Complex.I * z * ((u + c : Real) : Complex) =
        Complex.I * z * (u : Complex) + Complex.I * z * (c : Complex) := by
    push_cast
    ring
  rw [show u + c - c = u by ring, harg, Complex.exp_add]
  ring

theorem paperFT_mul_exp_half
    (f : Real → Complex) (z : Complex) :
    Zeta23.paperFT (fun u : Real => (Real.exp (u / 2) : Complex) * f u) z =
      Zeta23.paperFT f (z - Complex.I / 2) := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def]
  apply integral_congr_ae
  filter_upwards with u
  have harg :
      Complex.I * (z - Complex.I / 2) * (u : Complex) =
        ((u / 2 : Real) : Complex) + Complex.I * z * (u : Complex) := by
    calc
      Complex.I * (z - Complex.I / 2) * (u : Complex)
          = (Complex.I * z - (Complex.I * Complex.I) / 2) * (u : Complex) := by ring
      _ = (Complex.I * z + 1 / 2) * (u : Complex) := by
        rw [Complex.I_mul_I]
        ring
      _ = ((u / 2 : Real) : Complex) + Complex.I * z * (u : Complex) := by
        norm_num
        ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  ring

end
end KernelEsmeralda
