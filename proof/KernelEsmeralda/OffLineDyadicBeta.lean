import KernelEsmeralda.OffLineBetaBound
import KernelEsmeralda.CriticalLineDyadicCount
import KernelEsmeralda.ZetaDyadicCountUpper

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A beta-capped zero above positive height T inherits the quadratic Fourier
decay, with the horizontal displacement isolated in the factor
exp(sigma * emeraldLogRight n). -/
theorem emerald_zero_kernel_factor_le_at_positive_height_of_re_le
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (sigma : Real) (hre : (rho : Complex).re ≤ sigma)
    (hheight : T < (rho : Complex).im) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ ≤
      (Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
          T ^ 2 := by
  have hbase := emerald_zero_kernel_factor_mul_sq_le_of_re_le_scaled
    n hn rho sigma hre
  have himpos : 0 < (rho : Complex).im := lt_trans hT hheight
  have hTim : T ≤ |(rho : Complex).im| := by
    rw [abs_of_pos himpos]
    exact hheight.le
  have hTnorm : T ≤ ‖(rho : Complex)‖ :=
    hTim.trans (Complex.abs_im_le_norm (rho : Complex))
  have hsquare : T ^ 2 ≤ ‖(rho : Complex)‖ ^ 2 := by
    nlinarith [norm_nonneg (rho : Complex)]
  have hfactor0 :
      0 ≤ ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ := norm_nonneg _
  rw [le_div_iff₀ (sq_pos_of_pos hT)]
  exact (mul_le_mul_of_nonneg_left hsquare hfactor0).trans hbase

/-- The multiplicity-weighted explicit summand obeys the same beta-sensitive
dyadic decay. -/
theorem norm_emeraldExplicitTerm_le_mult_dyadic_of_re_le
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (sigma : Real) (hre : (rho : Complex).re ≤ sigma)
    (hheight : T < (rho : Complex).im) :
    ‖emeraldCriticalExplicitTerm n rho‖ ≤
      (Zeta23.zetaZeroConfig.mult rho : Real) *
        ((Real.exp (sigma * emeraldLogRight n) *
          (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
            T ^ 2) := by
  unfold emeraldCriticalExplicitTerm
  rw [norm_mul]
  have hmult : ‖(Zeta23.zetaZeroConfig.mult rho : Complex)‖ =
      (Zeta23.zetaZeroConfig.mult rho : Real) := by simp
  rw [hmult]
  exact mul_le_mul_of_nonneg_left
    (emerald_zero_kernel_factor_le_at_positive_height_of_re_le
      n hn T hT rho sigma hre hheight)
    (Nat.cast_nonneg _)

/-- Fourier-only dyadic block estimate for any finite family of zeta zeros
with real parts at most sigma. -/
theorem emeraldDyadicBetaBlock_bound_by_multiplicity
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T) (sigma : Real)
    (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re ≤ sigma ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
      ((Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
          T ^ 2) *
        (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
  let C : Real :=
    (Real.exp (sigma * emeraldLogRight n) *
      (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
        T ^ 2
  have hC : 0 ≤ C := by
    unfold C
    have hA := smoothstep_l1Deriv2_nonneg
    positivity
  calc
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
        ≤ ∑ rho ∈ s, ‖emeraldCriticalExplicitTerm n rho‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real) * C := by
          apply Finset.sum_le_sum
          intro rho hrho
          simpa [C] using norm_emeraldExplicitTerm_le_mult_dyadic_of_re_le
            n hn T hT rho sigma (hs rho hrho).1 (hs rho hrho).2.1
    _ = C * (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rho hrho
          ring
    _ = ((Real.exp (sigma * emeraldLogRight n) *
          (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
            T ^ 2) *
          (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) := by rfl

/-- The beta-sensitive block can be expressed directly in terms of the actual
Riemann-zeta dyadic counting function. -/
theorem emeraldDyadicBetaBlock_bound_by_N
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T) (sigma : Real)
    (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re ≤ sigma ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
      ((Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
          T ^ 2) *
        (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := by
  have hblock := emeraldDyadicBetaBlock_bound_by_multiplicity
    n hn T hT sigma s hs
  have hcount := dyadic_finset_mult_real_le_N T s
    (fun rho hrho => (hs rho hrho).2)
  have hC :
      0 ≤ (Real.exp (sigma * emeraldLogRight n) *
        (8 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real))) /
          T ^ 2 := by
    have hA := smoothstep_l1Deriv2_nonneg
    positivity
  exact hblock.trans (mul_le_mul_of_nonneg_left hcount hC)

/-- Combining the beta-sensitive Fourier bound with Riemann--von Mangoldt gives
O(exp(sigma log((n+1)^2)) * n log T / T) on a dyadic block. -/
theorem exists_emeraldDyadicBetaRvMBound :
    ∃ D T₀ : Real, 0 ≤ D ∧
      ∀ (n : Nat), 1 ≤ n → ∀ (sigma T : Real), T₀ ≤ T →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re ≤ sigma ∧
          T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          D * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log T / T := by
  obtain ⟨B, T₁, hB, hcount⟩ := exists_zeta_dyadic_count_upper
  let A : Real := Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep
  let D : Real := 8 * A * B
  let T₀ : Real := max T₁ 1
  refine ⟨D, T₀, ?_, ?_⟩
  · unfold D A
    exact mul_nonneg (mul_nonneg (by norm_num) smoothstep_l1Deriv2_nonneg) hB.le
  · intro n hn sigma T hT s hs
    have hT1 : T₁ ≤ T := le_trans (le_max_left _ _) hT
    have hTone : (1 : Real) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
    have hN := hcount T hT1
    have hblock := emeraldDyadicBetaBlock_bound_by_N
      n hn T hTpos sigma s hs
    let C : Real :=
      (Real.exp (sigma * emeraldLogRight n) * (8 * A * (n : Real))) / T ^ 2
    have hcoef : 0 ≤ C := by
      unfold C A
      have hA := smoothstep_l1Deriv2_nonneg
      positivity
    have hmul :
        C * (Zeta23.zetaZeroConfig.N T (2 * T) : Real) ≤
          C * (B * T * Real.log T) :=
      mul_le_mul_of_nonneg_left hN hcoef
    have hblock' :
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          C * (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := by
      simpa [C, A] using hblock
    calc
      ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖
          ≤ C * (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := hblock'
      _ ≤ C * (B * T * Real.log T) := hmul
      _ = D * Real.exp (sigma * emeraldLogRight n) *
            (n : Real) * Real.log T / T := by
          unfold C D
          field_simp [ne_of_gt hTpos] <;> ring

end
end KernelEsmeralda
