import KernelEsmeralda.ComplexPoissonTarget
import KernelEsmeralda.ComplexPoissonCore
import KernelEsmeralda.ComplexPoissonDecay

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace KernelEsmeralda

noncomputable section

/-- Full complex-parameter extension of the Poisson identity used by Zeta23.
This is the same compact-support/Fourier/Poisson proof as `Zeta23.Poisson`,
with the real sampling parameters replaced by fixed complex parameters. -/
theorem zeta23_taper_hasSum_phiHat_mul_complex
    {ϱ : Real → Real} {L w : Real}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (T : Real) (tau tau' : Complex) :
    HasSum
      (fun k : Int =>
        Zeta23.Taper.phiHat ϱ L w
            (tau - (((T + (k : Real) * (2 * Real.pi / L) : Real)) : Complex)) *
          Zeta23.Taper.phiHat ϱ L w
            (tau' - (((T + (k : Real) * (2 * Real.pi / L) : Real)) : Complex)))
      ((L : Complex) * Zeta23.Taper.Phi ϱ L w (tau - tau')) := by
  have hL : 0 < L := by linarith
  have hphiC := Zeta23.Taper.phi_continuous hϱ hw hwL
  have hsupp : ∀ u : Real, L / 2 ≤ |u| → Zeta23.Taper.phi ϱ L w u = 0 :=
    fun u hu => Zeta23.Taper.phi_eq_zero hϱ hw hu
  have heven : ∀ u : Real,
      Zeta23.Taper.phi ϱ L w (-u) = Zeta23.Taper.phi ϱ L w u :=
    fun u => Zeta23.Taper.phi_even u

  let C : Complex → Real := fun z =>
    Real.exp (|z.im| * (L / 2)) *
      (L + Zeta23.Taper.C1 ϱ L w)
  have hC1 : 0 ≤ Zeta23.Taper.C1 ϱ L w := by
    unfold Zeta23.Taper.C1
    positivity
  have hCnonneg : ∀ z : Complex, 0 ≤ C z := by
    intro z
    dsimp [C]
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg hL.le hC1)
  have hphi_bdd : ∀ z : Complex, ∀ s : Real,
      ‖Zeta23.Taper.phiHat ϱ L w (z - (s : Complex))‖ ≤ C z := by
    intro z s
    have hd := zeta23_taper_phiHat_complex_decay hϱ hw hwL z s
    have hfac : 1 ≤ 1 + (z.re - s) ^ 2 := by nlinarith [sq_nonneg (z.re - s)]
    have hm :
        ‖Zeta23.Taper.phiHat ϱ L w (z - (s : Complex))‖ * 1 ≤
          ‖Zeta23.Taper.phiHat ϱ L w (z - (s : Complex))‖ *
            (1 + (z.re - s) ^ 2) :=
      mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
    simpa [C] using hm.trans hd

  set G := ComplexPoissonCore.GauxC
    (Zeta23.Taper.phi ϱ L w) L T tau tau' with hG
  have hGc : Continuous G :=
    ComplexPoissonCore.GauxC_continuous hL hphiC hsupp

  have hGO : G =O[cocompact Real] fun x : Real => |x| ^ (-2 : Real) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : Real in cocompact Real, (1 : Real) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, ComplexPoissonCore.GauxC_eq_zero hL hsupp (by simpa using hx)]
    simp

  have hFO : 𝓕 G =O[cocompact Real] fun x : Real => |x| ^ (-2 : Real) := by
    apply Zeta23.Poisson.isBigO_of_decay
      (c := tau.re - T) (h := 2 * Real.pi / L)
      (C := C tau * C tau') (by positivity)
    intro x
    rw [hG, ComplexPoissonCore.fourier_GauxC hL hphiC hsupp x, norm_mul]
    have e1 :
        tau.re - T - x * (2 * Real.pi / L) =
          tau.re - (T + x * (2 * Real.pi / L)) := by ring
    rw [e1]
    calc
      ‖Zeta23.Taper.phiHat ϱ L w
          (tau - (((T + x * (2 * Real.pi / L) : Real)) : Complex))‖ *
          ‖Zeta23.Taper.phiHat ϱ L w
            (tau' - (((T + x * (2 * Real.pi / L) : Real)) : Complex))‖ *
          (1 + (tau.re - (T + x * (2 * Real.pi / L))) ^ 2)
          =
        (‖Zeta23.Taper.phiHat ϱ L w
            (tau - (((T + x * (2 * Real.pi / L) : Real)) : Complex))‖ *
          (1 + (tau.re - (T + x * (2 * Real.pi / L))) ^ 2)) *
          ‖Zeta23.Taper.phiHat ϱ L w
            (tau' - (((T + x * (2 * Real.pi / L) : Real)) : Complex))‖ := by ring
      _ ≤ C tau *
          ‖Zeta23.Taper.phiHat ϱ L w
            (tau' - (((T + x * (2 * Real.pi / L) : Real)) : Complex))‖ := by
        apply mul_le_mul_of_nonneg_right
          (zeta23_taper_phiHat_complex_decay hϱ hw hwL tau
            (T + x * (2 * Real.pi / L)))
          (norm_nonneg _)
      _ ≤ C tau * C tau' :=
        mul_le_mul_of_nonneg_left
          (hphi_bdd tau' (T + x * (2 * Real.pi / L)))
          (hCnonneg tau)

  have hsum : Summable fun n : Int => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)

  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    hGc one_lt_two hGO hsum 0

  have lhs : ∑' n : Int, G (0 + n) = G 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_add, hG, ComplexPoissonCore.GauxC_eq_zero hL hsupp]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn

  have rhs :
      ∑' n : Int, 𝓕 G n * fourier n ((0 : Real) : UnitAddCircle) =
        ∑' n : Int, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp

  rw [lhs, rhs] at key
  have hs : HasSum (fun n : Int => 𝓕 G n) (G 0) := by
    rw [key]
    exact hsum.hasSum
  rw [hG, ComplexPoissonCore.GauxC_zero heven] at hs
  change HasSum _
    ((L : Complex) * Zeta23.Taper.Phi ϱ L w (tau - tau'))
  convert hs using 1
  · funext k
    rw [ComplexPoissonCore.fourier_GauxC hL hphiC hsupp]
    rfl
  · rfl

/-- The previously isolated research target is now discharged directly. -/
theorem zeta23ComplexPoissonTarget_proved : Zeta23ComplexPoissonTarget := by
  unfold Zeta23ComplexPoissonTarget
  intro P T hP hwL tau tau'
  have hw : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
  have h2wL : 2 * P.w ≤ P.L T := by linarith [hP.one_le_w]
  have h := zeta23_taper_hasSum_phiHat_mul_complex
    hP.taper hw h2wL T tau tau'
  simpa [Zeta23.Params.phiHat, Zeta23.Params.Phi,
    Zeta23.Params.phi, Zeta23.Taper.phi,
    Zeta23.Params.tau, Zeta23.Params.hgrid,
    Zeta23.Taper.phiHat, Zeta23.Taper.Phi] using h

end
end KernelEsmeralda