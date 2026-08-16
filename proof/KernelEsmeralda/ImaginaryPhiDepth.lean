import Zeta23.Taper
import Zeta23.Taper.Fourier
import Mathlib.Analysis.SpecialFunctions.Arcosh

open Complex MeasureTheory Real Set Filter Topology

namespace KernelEsmeralda

noncomputable section

private theorem two_le_exp_add_exp_neg (x : Real) :
    2 ≤ Real.exp x + Real.exp (-x) := by
  have h := Real.one_le_cosh x
  rw [Real.cosh_eq] at h
  linarith

/-- On the imaginary axis, the Fourier transform `Phi = (phi^2)^` is the
Laplace transform of the even nonnegative taper square. -/
theorem zeta23_taper_Phi_imag_re_eq
    {ϱ : Real → Real} {L w y : Real}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    (Zeta23.Taper.Phi ϱ L w (Complex.I * (y : Complex))).re =
      ∫ u : Real,
        (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (-(y * u)) := by
  have hcomplex :
      Zeta23.Taper.Phi ϱ L w (Complex.I * (y : Complex)) =
        ((∫ u : Real,
          (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (-(y * u))) : Complex) := by
    unfold Zeta23.Taper.Phi Zeta23.paperFT
    rw [← Zeta23.integral_ofReal_C]
    congr 1 with u
    have harg :
        Complex.I * (Complex.I * (y : Complex)) * (u : Complex) =
          ((-(y * u) : Real) : Complex) := by
      push_cast
      rw [Complex.I_mul_I]
      ring
    rw [harg, ← Complex.ofReal_exp]
    norm_cast
  simpa using congrArg Complex.re hcomplex

/-- Evenness of the taper square makes the two opposite Laplace weights have
exactly the same total mass. -/
theorem zeta23_taper_laplace_even
    {ϱ : Real → Real} {L w y : Real} :
    (∫ u : Real,
      (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (-(y * u))) =
    ∫ u : Real,
      (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (y * u) := by
  have h := integral_neg_eq_self
    (μ := volume)
    (f := fun u : Real =>
      (Zeta23.Taper.phi ϱ L w u) ^ 2 * Real.exp (y * u))
  simpa [Zeta23.Taper.phi_even, mul_comm, mul_left_comm, mul_assoc] using h

/-- The imaginary-axis value of `Phi` is never smaller than its value at the
origin.  This is the unconditional analytic half of the off-line depth
mechanism: horizontal displacement increases the sampling energy on the RHS
of the complex Poisson identity, should that identity later be formalized. -/
theorem zeta23_taper_Phi_imag_re_ge_zero
    {ϱ : Real → Real} {L w y : Real}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Zeta23.Taper.PhiR ϱ L w 0 ≤
      (Zeta23.Taper.Phi ϱ L w (Complex.I * (y : Complex))).re := by
  let q : Real → Real := fun u => (Zeta23.Taper.phi ϱ L w u) ^ 2
  have hphiC := Zeta23.Taper.phi_continuous hϱ hw hwL
  have hphiS : HasCompactSupport (Zeta23.Taper.phi ϱ L w) :=
    Zeta23.Taper.phi_hasCompactSupport (L := L) hϱ hw
  have hqC : Continuous q := by
    dsimp [q]
    exact hphiC.pow 2
  have hqS : HasCompactSupport q := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc
    intro u hu
    have hqne := Function.mem_support.mp hu
    have hphine : Zeta23.Taper.phi ϱ L w u ≠ 0 := by
      intro hzero
      apply hqne
      simp [q, hzero]
    exact Zeta23.Taper.phi_support_subset hϱ hw
      (Function.mem_support.mpr hphine)
  have hqI : Integrable q := hqC.integrable_of_hasCompactSupport hqS
  have hmC : Continuous (fun u : Real => q u * Real.exp (-(y * u))) := by
    fun_prop
  have hpC : Continuous (fun u : Real => q u * Real.exp (y * u)) := by
    fun_prop
  have hmS : HasCompactSupport (fun u : Real => q u * Real.exp (-(y * u))) :=
    hqS.mul_right
  have hpS : HasCompactSupport (fun u : Real => q u * Real.exp (y * u)) :=
    hqS.mul_right
  have hmI : Integrable (fun u : Real => q u * Real.exp (-(y * u))) :=
    hmC.integrable_of_hasCompactSupport hmS
  have hpI : Integrable (fun u : Real => q u * Real.exp (y * u)) :=
    hpC.integrable_of_hasCompactSupport hpS
  have hpt : ∀ u : Real,
      2 * q u ≤ q u * Real.exp (-(y * u)) + q u * Real.exp (y * u) := by
    intro u
    have hq0 : 0 ≤ q u := by
      dsimp [q]
      positivity
    have he := two_le_exp_add_exp_neg (y * u)
    have hmul := mul_le_mul_of_nonneg_left he hq0
    calc
      2 * q u = q u * 2 := by ring
      _ ≤ q u * (Real.exp (y * u) + Real.exp (-(y * u))) := hmul
      _ = q u * Real.exp (-(y * u)) + q u * Real.exp (y * u) := by ring
  have hmono :
      ∫ u : Real, 2 * q u ≤
        ∫ u : Real, q u * Real.exp (-(y * u)) + q u * Real.exp (y * u) := by
    exact integral_mono (hqI.const_mul 2) (hmI.add hpI)
      (Eventually.of_forall hpt)
  have hsym := zeta23_taper_laplace_even (ϱ := ϱ) (L := L) (w := w) (y := y)
  rw [integral_const_mul, integral_add hmI hpI, ← hsym] at hmono
  have hbase :
      Zeta23.Taper.PhiR ϱ L w 0 = ∫ u : Real, q u := by
    unfold Zeta23.Taper.PhiR Zeta23.Taper.Phi Zeta23.paperFT
    rw [← Zeta23.integral_ofReal_C]
    norm_num
    rfl
  rw [zeta23_taper_Phi_imag_re_eq hϱ hw hwL, hbase]
  dsimp [q] at hmono ⊢
  linarith

/-- Consumer-facing specialization for the paper parameters. -/
theorem zeta23_Phi_imag_re_ge_aL
    {P : Zeta23.Params} {T y : Real}
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T) :
    P.a T * P.L T ≤
      (P.Phi T (Complex.I * (y : Complex))).re := by
  have h := zeta23_taper_Phi_imag_re_ge_zero
    (ϱ := P.ϱ) (L := P.L T) (w := P.w) (y := y)
    hP.taper (Zeta23.Params.w_pos hP) (Zeta23.Params.two_w_le hwL hP)
  have hzero := Zeta23.Params.PhiR_zero (P := P) (T := T) hP hwL
  change Zeta23.Taper.PhiR P.ϱ (P.L T) P.w 0 = P.a T * P.L T at hzero
  rw [hzero] at h
  simpa using h

end
end KernelEsmeralda
