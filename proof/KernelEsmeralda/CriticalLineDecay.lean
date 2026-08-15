import KernelEsmeralda.CriticalLineUniformBound
import KernelEsmeralda.TaperWidthLower
import KernelEsmeralda.TaperConstants
import KernelEsmeralda.ZetaTermBound

namespace KernelEsmeralda

noncomputable section

theorem smoothstep_l1Deriv2_nonneg :
    0 ≤ Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep := by
  unfold Zeta23.Taper.l1Deriv2
  exact MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)

theorem emeraldTaper_C1_le_eight_mul_n
    (n : Nat) (hn : 1 ≤ n) :
    Zeta23.Taper.C1 Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n) ≤
      8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hwpos := emeraldTaperWidth_pos n hn
  have hw := emeraldTaperWidth_ge_inv_four_n n hn
  have hscale :
      1 ≤ 4 * (n : Real) * emeraldTaperWidth n := by
    have hnonneg : 0 ≤ 4 * (n : Real) := by positivity
    have hm := mul_le_mul_of_nonneg_left hw hnonneg
    calc
      1 = (4 * (n : Real)) * (1 / (4 * (n : Real))) := by
        field_simp [hnpos.ne']
      _ ≤ (4 * (n : Real)) * emeraldTaperWidth n := hm
  rw [emeraldTaper_C1_exact n hn]
  rw [div_le_iff₀ hwpos]
  have hA0 : 0 ≤ Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep :=
    smoothstep_l1Deriv2_nonneg
  have hA : 0 ≤ 2 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep :=
    mul_nonneg (by norm_num) hA0
  have hm := mul_le_mul_of_nonneg_left hscale hA
  calc
    2 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep
        = (2 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep) * 1 := by ring
    _ ≤ (2 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep) *
          (4 * (n : Real) * emeraldTaperWidth n) := hm
    _ = (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real)) *
          emeraldTaperWidth n := by ring

theorem emerald_zero_kernel_factor_mul_sq_le_on_critical_line
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      Real.exp (emeraldLogRight n / 2) *
        Zeta23.Taper.C1 Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n) := by
  rw [norm_emerald_zero_kernel_factor, hrho]
  have hphi := emeraldTaper_phiHat_zero_bound_raw n hn rho
  have hreabs : |(rho : Complex).re| = (1 / 2 : Real) := by
    rw [hrho]
    norm_num
  rw [hreabs] at hphi
  have hcenter : 0 ≤ Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) := by positivity
  calc
    Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) *
          ‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2
        = Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) *
          (‖Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n)
            (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2) := by ring
    _ ≤ Real.exp ((1 / 2 : Real) * emeraldTaperCenter n) *
          (Real.exp ((1 / 2 : Real) * (emeraldTaperLength n / 2)) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n)) :=
        mul_le_mul_of_nonneg_left hphi hcenter
    _ = Real.exp (emeraldTaperCenter n / 2) *
          (Real.exp (emeraldTaperLength n / 4) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n)) := by ring
    _ = (Real.exp (emeraldTaperCenter n / 2) *
          Real.exp (emeraldTaperLength n / 4)) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n) := by ring
    _ = Real.exp (emeraldTaperCenter n / 2 + emeraldTaperLength n / 4) *
            Zeta23.Taper.C1 Zeta23.Taper.smoothstep
              (emeraldTaperLength n) (emeraldTaperWidth n) := by
          rw [Real.exp_add]
    _ = Real.exp (emeraldLogRight n / 2) *
          Zeta23.Taper.C1 Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n) := by
          rw [emeraldTaper_center_half_add_length_quarter]

theorem emerald_zero_kernel_factor_mul_sq_le_sixteen_n_sq
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2 ≤
      16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2 := by
  have hmain := emerald_zero_kernel_factor_mul_sq_le_on_critical_line n hn rho hrho
  rw [exp_emeraldLogRight_half_eq_succ] at hmain
  have hC := emeraldTaper_C1_le_eight_mul_n n hn
  have hsucc : (((n + 1 : Nat) : Real)) ≤ 2 * (n : Real) := by
    push_cast
    have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    linarith
  have hA0 : 0 ≤ Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep :=
    smoothstep_l1Deriv2_nonneg
  have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg n
  have hA : 0 ≤ 8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) :=
    mul_nonneg (mul_nonneg (by norm_num) hA0) hn0
  have hsucc0 : 0 ≤ (((n + 1 : Nat) : Real)) := Nat.cast_nonneg (n + 1)
  calc
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ * ‖(rho : Complex)‖ ^ 2
      ≤ (((n + 1 : Nat) : Real)) *
          Zeta23.Taper.C1 Zeta23.Taper.smoothstep
            (emeraldTaperLength n) (emeraldTaperWidth n) := hmain
    _ ≤ (((n + 1 : Nat) : Real)) *
          (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real)) :=
        mul_le_mul_of_nonneg_left hC hsucc0
    _ ≤ (2 * (n : Real)) *
          (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real)) :=
        mul_le_mul_of_nonneg_right hsucc hA
    _ = 16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2 := by ring

end
end KernelEsmeralda
