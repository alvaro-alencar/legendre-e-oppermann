import Zeta23.Poisson

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace KernelEsmeralda
namespace ComplexPoissonCore

noncomputable section

/-- Complex-parameter analogue of Zeta23.Poisson.gInt.  Only the sampling
parameters are complex; the physical variables xi,u and scale L,T remain real. -/
noncomputable def gIntC
    (phi : Real → Real) (L T : Real) (tau tau' : Complex)
    (xi u : Real) : Complex :=
  (L : Complex) *
    ((phi u : Complex) * (phi (L * xi - u) : Complex) *
      Complex.exp
        (Complex.I *
          (tau * (u : Complex) +
            tau' * ((L * xi - u : Real) : Complex) -
            ((T * L * xi : Real) : Complex))))

/-- The auxiliary compactly supported function for complex sampling parameters. -/
noncomputable def GauxC
    (phi : Real → Real) (L T : Real) (tau tau' : Complex)
    (xi : Real) : Complex :=
  ∫ u, gIntC phi L T tau tau' xi u

theorem gIntC_eq_zero_of_not_mem
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0)
    {xi u : Real} (h : ¬ (|xi| < 1 ∧ |u| < L / 2)) :
    gIntC phi L T tau tau' xi u = 0 := by
  unfold gIntC
  by_cases hu : |u| < L / 2
  · have hxi : 1 ≤ |xi| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have hfar : L / 2 ≤ |L * xi - u| := by
      have h4 : |L * xi| - |u| ≤ |L * xi - u| :=
        abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h4
      nlinarith
    rw [hsupp _ hfar]
    simp
  · rw [hsupp u (not_lt.mp hu)]
    simp

theorem gIntC_continuous
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hphic : Continuous phi) :
    Continuous (Function.uncurry (gIntC phi L T tau tau')) := by
  unfold gIntC Function.uncurry
  fun_prop

theorem gIntC_hasCompactSupport
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0) :
    HasCompactSupport (Function.uncurry (gIntC phi L T tau tau')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := (-1 : Real)) (b := 1)).prod
      (isCompact_Icc (a := -(L / 2)) (b := L / 2))) ?_
  rintro ⟨xi, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (gIntC_eq_zero_of_not_mem hL hsupp _)
  rintro ⟨h1, h2⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le xi], by linarith [le_abs_self xi]⟩,
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

theorem gIntC_integrable_prod
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L) (hphic : Continuous phi)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0) :
    Integrable (Function.uncurry (gIntC phi L T tau tau'))
      (volume.prod volume) :=
  (gIntC_continuous hphic).integrable_of_hasCompactSupport
    (gIntC_hasCompactSupport hL hsupp)

theorem GauxC_continuous
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L) (hphic : Continuous phi)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0) :
    Continuous (GauxC phi L T tau tau') := by
  have hrep : GauxC phi L T tau tau' =
      fun xi => ∫ u in Icc (-(L / 2)) (L / 2),
        gIntC phi L T tau tau' xi u := by
    funext xi
    unfold GauxC
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply gIntC_eq_zero_of_not_mem hL hsupp
    rintro ⟨-, h2⟩
    apply hu
    rw [mem_Icc]
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [hrep]
  exact continuous_parametric_integral_of_continuous
    (gIntC_continuous hphic) isCompact_Icc

theorem GauxC_eq_zero
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0)
    {xi : Real} (hxi : 1 ≤ |xi|) :
    GauxC phi L T tau tau' xi = 0 := by
  unfold GauxC
  rw [← integral_zero]
  congr 1 with u
  apply gIntC_eq_zero_of_not_mem hL hsupp
  rintro ⟨h1, -⟩
  linarith

/-- The zero-frequency identity survives unchanged for complex tau,tau'. -/
theorem GauxC_zero
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (heven : ∀ u, phi (-u) = phi u) :
    GauxC phi L T tau tau' 0 =
      (L : Complex) *
        Zeta23.paperFT (fun u => ((phi u ^ 2 : Real) : Complex))
          (tau - tau') := by
  unfold GauxC gIntC
  rw [Zeta23.paperFT_def, Zeta23.integral_const_mul_C]
  congr 1
  congr 1 with u
  simp only [mul_zero, zero_sub, heven]
  push_cast
  ring_nf

/-- Complex-parameter exponent bookkeeping for the Poisson/Fubini step. -/
theorem cexp_bookkeepingC
    {L T : Real} {tau tau' : Complex}
    (hL : L ≠ 0) (xi u w : Real) :
    Complex.exp
        (Complex.I *
          (tau * (u : Complex) +
            tau' * ((L * xi - u : Real) : Complex) -
            ((T * L * xi : Real) : Complex))) *
      Complex.exp (((-2 * Real.pi * xi * w : Real) : Complex) * Complex.I) =
    Complex.exp
        (Complex.I *
          (tau - (((T + w * (2 * Real.pi / L) : Real)) : Complex)) *
          (u : Complex)) *
      Complex.exp
        (Complex.I *
          (tau' - (((T + w * (2 * Real.pi / L) : Real)) : Complex)) *
          ((L * xi - u : Real) : Complex)) := by
  have hLC : (L : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Fubini computation with complex sampling parameters:
`Fourier(G_C)(w) = phiHat(tau-tau_w) * phiHat(tau'-tau_w)` for real w. -/
theorem fourier_GauxC
    {phi : Real → Real} {L T : Real} {tau tau' : Complex}
    (hL : 0 < L) (hphic : Continuous phi)
    (hsupp : ∀ u, L / 2 ≤ |u| → phi u = 0)
    (w : Real) :
    𝓕 (GauxC phi L T tau tau') w =
      Zeta23.paperFT (fun u => (phi u : Complex))
        (tau - (((T + w * (2 * Real.pi / L) : Real)) : Complex)) *
      Zeta23.paperFT (fun u => (phi u : Complex))
        (tau' - (((T + w * (2 * Real.pi / L) : Real)) : Complex)) := by
  set alpha : Complex :=
    tau - (((T + w * (2 * Real.pi / L) : Real)) : Complex) with halpha
  set beta : Complex :=
    tau' - (((T + w * (2 * Real.pi / L) : Real)) : Complex) with hbeta
  set J : Real → Real → Complex := fun xi u =>
    Complex.exp (((-2 * Real.pi * xi * w : Real) : Complex) * Complex.I) *
      gIntC phi L T tau tau' xi u with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have hg := gIntC_continuous
        (L := L) (T := T) (tau := tau) (tau' := tau') hphic
      simp only [hJ]
      apply Continuous.mul _ hg
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply (gIntC_hasCompactSupport
      (T := T) (tau := tau) (tau' := tau') hL hsupp).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 :
      (fun xi : Real =>
        Complex.exp (((-2 * Real.pi * xi * w : Real) : Complex) * Complex.I) •
          GauxC phi L T tau tau' xi) =
      fun xi => ∫ u, J xi u := by
    funext xi
    rw [smul_eq_mul, GauxC, hJ]
    beta_reduce
    rw [Zeta23.integral_const_mul_C]
  rw [step1]
  rw [integral_integral_swap hJint]
  have step3 : ∀ u : Real, ∫ xi, J xi u =
      (phi u : Complex) * Complex.exp (Complex.I * alpha * (u : Complex)) *
        Zeta23.paperFT (fun v => (phi v : Complex)) beta := by
    intro u
    set F0 : Real → Complex := fun v =>
      (phi v : Complex) * Complex.exp (Complex.I * beta * (v : Complex)) with hF0
    have hpt : ∀ xi : Real, J xi u =
        (phi u : Complex) * Complex.exp (Complex.I * alpha * (u : Complex)) *
          ((L : Complex) * ((fun y : Real => F0 (y - u)) (L * xi))) := by
      intro xi
      simp only [hJ, gIntC, hF0]
      have hb := cexp_bookkeepingC
        (T := T) (tau := tau) (tau' := tau') hL.ne' xi u w
      rw [← halpha, ← hbeta] at hb
      calc
        Complex.exp (((-2 * Real.pi * xi * w : Real) : Complex) * Complex.I) *
            ((L : Complex) *
              ((phi u : Complex) * (phi (L * xi - u) : Complex) *
                Complex.exp
                  (Complex.I *
                    (tau * (u : Complex) +
                      tau' * ((L * xi - u : Real) : Complex) -
                      ((T * L * xi : Real) : Complex))))) =
          (L : Complex) * (phi u : Complex) * (phi (L * xi - u) : Complex) *
            (Complex.exp
              (Complex.I *
                (tau * (u : Complex) +
                  tau' * ((L * xi - u : Real) : Complex) -
                  ((T * L * xi : Real) : Complex))) *
              Complex.exp (((-2 * Real.pi * xi * w : Real) : Complex) * Complex.I)) := by ring
        _ = (L : Complex) * (phi u : Complex) * (phi (L * xi - u) : Complex) *
            (Complex.exp (Complex.I * alpha * (u : Complex)) *
              Complex.exp
                (Complex.I * beta * ((L * xi - u : Real) : Complex))) := by
              rw [hb]
        _ = _ := by push_cast; ring
    have hint : ∫ xi, J xi u =
        ∫ xi,
          (phi u : Complex) * Complex.exp (Complex.I * alpha * (u : Complex)) *
            ((L : Complex) * ((fun y : Real => F0 (y - u)) (L * xi))) := by
      congr 1 with xi
      exact hpt xi
    rw [hint, Zeta23.integral_const_mul_C, Zeta23.integral_const_mul_C,
      Measure.integral_comp_mul_left (fun y : Real => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, Zeta23.paperFT_def,
      abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, Complex.ofReal_inv,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  rw [Zeta23.integral_mul_const_C, Zeta23.paperFT_def, Zeta23.paperFT_def]

end
end ComplexPoissonCore
end KernelEsmeralda
