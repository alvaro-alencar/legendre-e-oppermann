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

end
end ComplexPoissonCore
end KernelEsmeralda
