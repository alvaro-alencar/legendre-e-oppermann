import KernelEsmeralda.EmeraldTaper
import KernelEsmeralda.PaperFTShift
import KernelEsmeralda.ResearchTarget

namespace KernelEsmeralda

noncomputable section

theorem emeraldPaperFT_eq_paperFT (K : Real → Real) (z : Complex) :
    emeraldPaperFT K z = Zeta23.paperFT (emeraldWeilTest K) z := rfl

theorem emeraldTaper_paperFT_formula (n : Nat) (z : Complex) :
    emeraldPaperFT (emeraldTaperWeight n) z =
      Complex.exp
        (Complex.I * (z - Complex.I / 2) * (emeraldTaperCenter n : Complex)) *
      Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n) (z - Complex.I / 2) := by
  rw [emeraldPaperFT_eq_paperFT]
  have htest :
      emeraldWeilTest (emeraldTaperWeight n) =
        fun u : Real =>
          (Real.exp (u / 2) : Complex) * (emeraldTaperWeight n u : Complex) := by
    funext u
    simp [emeraldWeilTest, emeraldTilt]
  rw [htest, paperFT_mul_exp_half]
  let f : Real → Complex := fun v =>
    (Zeta23.Taper.phi Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n) v : Complex)
  have htrans := paperFT_translate
    (f := f)
    (c := emeraldTaperCenter n)
    (z := z - Complex.I / 2)
  simpa [f, emeraldTaperWeight, Zeta23.Taper.phiHat] using htrans

end
end KernelEsmeralda
