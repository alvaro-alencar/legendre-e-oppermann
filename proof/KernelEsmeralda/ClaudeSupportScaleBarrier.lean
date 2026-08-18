import KernelEsmeralda.ClaudeSupportBarrier

open Set

namespace KernelEsmeralda

noncomputable section

/-- Up to spectral height 2π n², a valid Zeta23 bandwidth parameter has
support length no larger than log(n²), the left edge of the Legendre window.
This uses the paper's exact scale l(T)=log(T/(2π)), not the approximation log T. -/
theorem zeta23_valid_L_le_emeraldLogLeft_of_T_le_two_pi_square
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n)
    (T : Real) (hTpos : 0 < T)
    (hT : T ≤ 2 * Real.pi * lowerSquare n) :
    P.L T ≤ emeraldLogLeft n := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hsquarepos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hdenpos : (0 : Real) < 2 * Real.pi := by positivity
  have hfracpos : 0 < T / (2 * Real.pi) := div_pos hTpos hdenpos
  have hfrac_le : T / (2 * Real.pi) ≤ lowerSquare n := by
    rw [div_le_iff₀ hdenpos]
    calc
      T ≤ 2 * Real.pi * lowerSquare n := hT
      _ = lowerSquare n * (2 * Real.pi) := by ring
  have hl_le_left : Zeta23.l T ≤ emeraldLogLeft n := by
    unfold Zeta23.l emeraldLogLeft
    exact Real.strictMonoOn_log.monotoneOn hfracpos hsquarepos hfrac_le
  have hnR : (1 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogn : 0 < Real.log (n : Real) := Real.log_pos hnR
  have hleftpos : 0 < emeraldLogLeft n := by
    rw [emeraldLogLeft_eq_two_log_n n hn1]
    linarith
  by_cases hl : 0 ≤ Zeta23.l T
  · have hLle : P.L T ≤ Zeta23.l T := by
      unfold Zeta23.Params.L
      have hmul := mul_le_mul_of_nonneg_right hP.lam_le_one hl
      simpa using hmul
    exact hLle.trans hl_le_left
  · have hlneg : Zeta23.l T < 0 := lt_of_not_ge hl
    have hLneg : P.L T < 0 := by
      unfold Zeta23.Params.L
      exact mul_neg_of_pos_of_neg hP.lam_pos hlneg
    exact le_of_lt (hLneg.trans hleftpos)

/-- Consequently, at every positive height T ≤ 2π n², a Claude-compatible
Weil convolution is zero throughout the interior of the positive logarithmic
Legendre window. -/
theorem zeta23_valid_weilTest_zero_inside_legendre_window_of_T_le_two_pi_square
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n)
    (T : Real) (hTpos : 0 < T)
    (hT : T ≤ 2 * Real.pi * lowerSquare n)
    (f g : Real → Complex)
    (hfs : tsupport f ⊆ Icc (-(P.L T / 2)) (P.L T / 2))
    (hgs : tsupport g ⊆ Icc (-(P.L T / 2)) (P.L T / 2))
    {x : Real} (hx : emeraldLogLeft n < x) :
    Zeta23.EF.weilTest f g x = 0 := by
  have hL := zeta23_valid_L_le_emeraldLogLeft_of_T_le_two_pi_square
    P hP n hn T hTpos hT
  exact weilTest_eq_zero_of_support_right hfs hgs (lt_of_le_of_lt hL hx)

/-- Contrapositive form: a direct Claude-compatible Weil test that is nonzero
at any logarithmic point strictly beyond n² must use spectral height
T > 2π n².  This is a support/bandwidth necessity theorem, not a universal
impossibility statement for indirect arguments. -/
theorem two_pi_square_lt_height_of_valid_weilTest_nonzero_inside_legendre_window
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n)
    (T : Real) (hTpos : 0 < T)
    (f g : Real → Complex)
    (hfs : tsupport f ⊆ Icc (-(P.L T / 2)) (P.L T / 2))
    (hgs : tsupport g ⊆ Icc (-(P.L T / 2)) (P.L T / 2))
    {x : Real} (hx : emeraldLogLeft n < x)
    (hne : Zeta23.EF.weilTest f g x ≠ 0) :
    2 * Real.pi * lowerSquare n < T := by
  by_contra hnot
  have hTle : T ≤ 2 * Real.pi * lowerSquare n := le_of_not_gt hnot
  exact hne (zeta23_valid_weilTest_zero_inside_legendre_window_of_T_le_two_pi_square
    P hP n hn T hTpos hTle f g hfs hgs hx)

end
end KernelEsmeralda
