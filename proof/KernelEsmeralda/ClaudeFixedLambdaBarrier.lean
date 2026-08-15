import KernelEsmeralda.ClaudeSupportScaleBarrier
import KernelEsmeralda.CriticalLineUniformBound

open Set

namespace KernelEsmeralda

noncomputable section

/-- At the square spectral scale T = 2π (n+1)^2, the paper logarithm is
exactly the right logarithmic endpoint of the Legendre window. -/
theorem zeta23_l_at_two_pi_upperSquare (n : Nat) :
    Zeta23.l (2 * Real.pi * upperSquare n) = emeraldLogRight n := by
  have hden : (2 * Real.pi : Real) ≠ 0 := by positivity
  unfold Zeta23.l emeraldLogRight
  congr 1
  field_simp [hden]

/-- Consequently the support length of a fixed Zeta23 parameter at
T = 2π (n+1)^2 is λ times the right endpoint log((n+1)^2). -/
theorem zeta23_L_at_two_pi_upperSquare (P : Zeta23.Params) (n : Nat) :
    P.L (2 * Real.pi * upperSquare n) =
      P.lam * emeraldLogRight n := by
  unfold Zeta23.Params.L
  rw [zeta23_l_at_two_pi_upperSquare]

/-- If the fixed-lambda loss `(1-λ) log((n+1)^2)` is larger than the whole
Legendre logarithmic window, then the Claude support already ends before
log(n^2).  The elementary estimate `window length ≤ 2/n` makes the criterion
explicit. -/
theorem zeta23_fixed_lambda_L_lt_emeraldLogLeft_of_gap
    (P : Zeta23.Params) (n : Nat) (hn : 1 ≤ n)
    (hgap : 2 / (n : Real) <
      (1 - P.lam) * emeraldLogRight n) :
    P.L (2 * Real.pi * upperSquare n) < emeraldLogLeft n := by
  have hlen := emeraldTaperLength_le_two_div_n n hn
  have hwindow :
      emeraldTaperLength n < (1 - P.lam) * emeraldLogRight n :=
    lt_of_le_of_lt hlen hgap
  rw [zeta23_L_at_two_pi_upperSquare]
  unfold emeraldTaperLength at hwindow
  linarith

/-- A convenient fully explicit sufficient condition for the previous gap.
For fixed λ<1, the right side is a constant threshold in n. -/
theorem zeta23_fixed_lambda_gap_of_large_n
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam < 1)
    (n : Nat) (hn : 1 ≤ n)
    (hlarge : 2 / ((1 - P.lam) * Real.log 4) < (n : Real)) :
    2 / (n : Real) < (1 - P.lam) * emeraldLogRight n := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hdelta : 0 < (1 - P.lam) := sub_pos.mpr hlam
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hden : 0 < (1 - P.lam) * Real.log 4 := mul_pos hdelta hlog4
  have hsucc : (2 : Real) ≤ (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hsquare4 : (4 : Real) ≤ upperSquare n := by
    unfold upperSquare
    nlinarith
  have hsquarepos : 0 < upperSquare n := lt_of_lt_of_le (by norm_num) hsquare4
  have hlogle : Real.log 4 ≤ emeraldLogRight n := by
    unfold emeraldLogRight
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hsquarepos hsquare4
  have htwo : 2 < (n : Real) * ((1 - P.lam) * Real.log 4) := by
    rw [div_lt_iff₀ hden] at hlarge
    simpa [mul_comm] using hlarge
  have hsmall : 2 / (n : Real) < (1 - P.lam) * Real.log 4 := by
    rw [div_lt_iff₀ hnpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwo
  have hmul :
      (1 - P.lam) * Real.log 4 ≤
        (1 - P.lam) * emeraldLogRight n :=
    mul_le_mul_of_nonneg_left hlogle hdelta.le
  exact hsmall.trans_le hmul

/-- Therefore, for every fixed paper parameter with λ<1, once n is beyond
the explicit threshold above, a Claude-compatible Weil convolution at the
square scale T = 2π (n+1)^2 vanishes throughout the positive interior of the
Legendre logarithmic window.  To keep touching the window for arbitrarily
large n, λ cannot stay fixed below 1. -/
theorem zeta23_fixed_lambda_weilTest_zero_at_square_scale
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam < 1)
    (n : Nat) (hn : 2 ≤ n)
    (hlarge : 2 / ((1 - P.lam) * Real.log 4) < (n : Real))
    (f g : Real → Complex)
    (hfs : tsupport f ⊆
      Icc (-(P.L (2 * Real.pi * upperSquare n) / 2))
          (P.L (2 * Real.pi * upperSquare n) / 2))
    (hgs : tsupport g ⊆
      Icc (-(P.L (2 * Real.pi * upperSquare n) / 2))
          (P.L (2 * Real.pi * upperSquare n) / 2))
    {x : Real} (hx : emeraldLogLeft n < x) :
    Zeta23.EF.weilTest f g x = 0 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hgap := zeta23_fixed_lambda_gap_of_large_n P hP hlam n hn1 hlarge
  have hL := zeta23_fixed_lambda_L_lt_emeraldLogLeft_of_gap P n hn1 hgap
  exact weilTest_eq_zero_of_support_right hfs hgs (lt_trans hL hx)

/-- Eventual form of the fixed-lambda obstruction.  Every single fixed
parameter with λ<1 has a finite threshold after which its square-scale support
ends strictly before the Legendre logarithmic window. -/
theorem exists_zeta23_fixed_lambda_square_scale_threshold
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∃ N : Nat, 2 ≤ N ∧ ∀ n : Nat, N ≤ n →
      P.L (2 * Real.pi * upperSquare n) < emeraldLogLeft n := by
  obtain ⟨M, hM⟩ := exists_nat_gt
    (2 / ((1 - P.lam) * Real.log 4) : Real)
  let N : Nat := max 2 M
  refine ⟨N, ?_, ?_⟩
  · exact le_max_left 2 M
  · intro n hnN
    have h2n : 2 ≤ n := le_trans (le_max_left 2 M) hnN
    have hMn : M ≤ n := le_trans (le_max_right 2 M) hnN
    have hlarge :
        2 / ((1 - P.lam) * Real.log 4) < (n : Real) := by
      exact lt_of_lt_of_le hM (by exact_mod_cast hMn)
    have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) h2n
    have hgap := zeta23_fixed_lambda_gap_of_large_n P hP hlam n hn1 hlarge
    exact zeta23_fixed_lambda_L_lt_emeraldLogLeft_of_gap P n hn1 hgap

end
end KernelEsmeralda
