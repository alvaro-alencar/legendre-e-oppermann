import KernelEsmeralda.ImaginaryPhiDepth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex MeasureTheory Real Set Filter Topology

namespace KernelEsmeralda

noncomputable section

/-- A fixed slice of the left plateau already forces exponential growth of
`Re Phi(i y)`.  The loss in the exponent depends only on the taper width `w`,
while the positive term uses the full half-length `L/2`. -/
theorem zeta23_taper_Phi_imag_re_ge_edge
    {ϱ : Real → Real} {L w y : Real}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w)
    (hwL : 8 * w ≤ L) (hy : 0 ≤ y) :
    (w / 2) * Real.exp (y * (L / 2 - 3 * w / 2)) ≤
      (Zeta23.Taper.Phi ϱ L w (Complex.I * (y : Complex))).re := by
  let a : Real := -(L / 2) + w
  let b : Real := -(L / 2) + 3 * w / 2
  let c : Real := Real.exp (y * (L / 2 - 3 * w / 2))
  let g : Real → Real := fun u =>
    (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (-(y * u))

  have h2wL : 2 * w ≤ L := by linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hb0 : b ≤ 0 := by
    dsimp [b]
    linarith
  have hwidth : b - a = w / 2 := by
    dsimp [a, b]
    ring

  have hgC : Continuous g := by
    dsimp [g]
    exact ((Zeta23.Taper.phi_continuous hϱ hw h2wL).pow 2).mul (by fun_prop)
  have hgS : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc
    intro u hu
    have hgne := Function.mem_support.mp hu
    have hphine : Zeta23.Taper.phi ϱ L w u ≠ 0 := by
      intro hzero
      apply hgne
      simp [g, hzero]
    exact Zeta23.Taper.phi_support_subset hϱ hw
      (Function.mem_support.mpr hphine)
  have hgI : Integrable g := hgC.integrable_of_hasCompactSupport hgS
  have hgnonneg : ∀ u : Real, 0 ≤ g u := by
    intro u
    dsimp [g]
    positivity

  have hpoint : ∀ u ∈ Ioc a b, c ≤ g u := by
    intro u hu
    have hu0 : u ≤ 0 := hu.2.trans hb0
    have habs : |u| ≤ L / 2 - w := by
      rw [abs_of_nonpos hu0]
      have hua : a < u := hu.1
      dsimp [a] at hua
      linarith
    have hphi := Zeta23.Taper.phi_eq_one hϱ hw habs
    have hedge : L / 2 - 3 * w / 2 ≤ -u := by
      have hub : u ≤ b := hu.2
      dsimp [b] at hub
      linarith
    have hmul := mul_le_mul_of_nonneg_left hedge hy
    have hexp : c ≤ Real.exp (-(y * u)) := by
      dsimp [c]
      apply Real.exp_le_exp.mpr
      calc
        y * (L / 2 - 3 * w / 2) ≤ y * (-u) := hmul
        _ = -(y * u) := by ring
    dsimp [g]
    rw [hphi]
    simpa using hexp

  have hrestricted :
      (∫ _u in Ioc a b, c) ≤ ∫ u in Ioc a b, g u := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Eventually.of_forall (fun _ => by dsimp [c]; positivity)
    · exact hgI.integrableOn
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall (fun u hu => hpoint u hu)

  have hconst : (∫ _u in Ioc a b, c) = (w / 2) * c := by
    rw [← intervalIntegral.integral_of_le hab]
    simp [hwidth]

  have hglobal :
      (∫ u in Ioc a b, g u) ≤ ∫ u : Real, g u :=
    MeasureTheory.setIntegral_le_integral hgI
      (Eventually.of_forall hgnonneg)

  rw [zeta23_taper_Phi_imag_re_eq hϱ hw h2wL]
  change (w / 2) * c ≤ ∫ u : Real, g u
  calc
    (w / 2) * c = ∫ _u in Ioc a b, c := hconst.symm
    _ ≤ ∫ u in Ioc a b, g u := hrestricted
    _ ≤ ∫ u : Real, g u := hglobal

end
end KernelEsmeralda
