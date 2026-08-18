import KernelEsmeralda.ComplexPoissonCore
import Zeta23.Taper.Strip

open Complex MeasureTheory Real Set Filter Topology Asymptotics

namespace KernelEsmeralda

noncomputable section

/-- Complex analogue of `Zeta23.Taper.phiHat_decay`.  For a fixed complex
sampling point `tau`, horizontal real translates retain quadratic decay.  The
only new cost is the Paley-Wiener factor coming from the fixed imaginary part.
-/
theorem zeta23_taper_phiHat_complex_decay
    {ϱ : Real → Real} {L w : Real}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (tau : Complex) (s : Real) :
    ‖Zeta23.Taper.phiHat ϱ L w (tau - (s : Complex))‖ *
        (1 + (tau.re - s) ^ 2) ≤
      Real.exp (|tau.im| * (L / 2)) *
        (L + Zeta23.Taper.C1 ϱ L w) := by
  let z : Complex := tau - (s : Complex)
  have h0 := Zeta23.Taper.norm_phiHat_le hϱ hw hwL z
  have h2 := Zeta23.Taper.norm_phiHat_mul_sq_le hϱ hw hwL z
  have him : |z.im| = |tau.im| := by
    simp [z]
  rw [him] at h0 h2
  have hre : |tau.re - s| ≤ ‖z‖ := by
    have hz := Complex.abs_re_le_norm z
    have hzre : z.re = tau.re - s := by simp [z]
    simpa [hzre] using hz
  have hsq : (tau.re - s) ^ 2 ≤ ‖z‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg (tau.re - s)) hre 2
    rw [sq_abs] at hs
    exact hs
  have hmul :
      ‖Zeta23.Taper.phiHat ϱ L w z‖ * (tau.re - s) ^ 2 ≤
        ‖Zeta23.Taper.phiHat ϱ L w z‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  change
    ‖Zeta23.Taper.phiHat ϱ L w z‖ * (1 + (tau.re - s) ^ 2) ≤ _
  calc
    ‖Zeta23.Taper.phiHat ϱ L w z‖ * (1 + (tau.re - s) ^ 2)
        = ‖Zeta23.Taper.phiHat ϱ L w z‖ +
          ‖Zeta23.Taper.phiHat ϱ L w z‖ * (tau.re - s) ^ 2 := by ring
    _ ≤ Real.exp (|tau.im| * (L / 2)) * L +
          Real.exp (|tau.im| * (L / 2)) * Zeta23.Taper.C1 ϱ L w :=
      add_le_add h0 (hmul.trans h2)
    _ = Real.exp (|tau.im| * (L / 2)) *
          (L + Zeta23.Taper.C1 ϱ L w) := by ring

end
end KernelEsmeralda
