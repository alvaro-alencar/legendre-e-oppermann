import KernelEsmeralda.EmeraldTaper
import Zeta23.Taper.Norms

namespace KernelEsmeralda

noncomputable section

theorem emeraldTaper_C1_exact (n : Nat) (hn : 1 ≤ n) :
    Zeta23.Taper.C1 Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n) =
      2 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep /
        emeraldTaperWidth n := by
  simpa [Zeta23.Taper.C1] using
    Zeta23.Taper.integral_abs_deriv2_phi
      Zeta23.Taper.taperProfile_smoothstep
      (emeraldTaperWidth_pos n hn)
      (two_mul_emeraldTaperWidth_le_length n hn)

end
end KernelEsmeralda
