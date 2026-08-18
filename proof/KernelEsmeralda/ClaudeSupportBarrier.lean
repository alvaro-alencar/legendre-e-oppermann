import Zeta23.ExplicitFormula
import KernelEsmeralda.CriticalLineFrequency

open Set

namespace KernelEsmeralda

noncomputable section

/-- A Weil convolution built from two tests supported in [-L/2,L/2]
vanishes strictly to the right of L.  This is the support geometry behind
the paper's bandwidth parameter. -/
theorem weilTest_eq_zero_of_support_right
    {f g : Real → Complex} {L x : Real}
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2))
    (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2))
    (hx : L < x) :
    Zeta23.EF.weilTest f g x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxmem
  have hxI := Zeta23.EF.tsupport_weilTest_subset hfs hgs hxmem
  exact (not_le_of_gt hx) hxI.2

/-- At the natural spectral height T=n, every valid Zeta23 paper parameter
has support length strictly smaller than log(n^2), the left edge of the
Legendre prime window.  The proof allows the paper logarithm l(n) to be
negative for small n; in that case the inequality is even stronger. -/
theorem zeta23_valid_L_at_n_lt_emeraldLogLeft
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n) :
    P.L (n : Real) < emeraldLogLeft n := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnR : (1 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogn : 0 < Real.log (n : Real) := Real.log_pos hnR
  have hden : (1 : Real) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hfrac : (n : Real) / (2 * Real.pi) < (n : Real) := by
    rw [div_lt_iff₀ (by positivity : (0 : Real) < 2 * Real.pi)]
    have hmul := mul_lt_mul_of_pos_left hden hnpos
    simpa [mul_assoc] using hmul
  have hfracpos : (0 : Real) < (n : Real) / (2 * Real.pi) := by positivity
  have hl_lt_log : Zeta23.l (n : Real) < Real.log (n : Real) := by
    unfold Zeta23.l
    exact Real.strictMonoOn_log hfracpos hnpos hfrac
  rw [emeraldLogLeft_eq_two_log_n n hn1]
  by_cases hl : 0 ≤ Zeta23.l (n : Real)
  · have hLle : P.L (n : Real) ≤ Zeta23.l (n : Real) := by
      unfold Zeta23.Params.L
      have hmul := mul_le_mul_of_nonneg_right hP.lam_le_one hl
      simpa using hmul
    linarith
  · have hlneg : Zeta23.l (n : Real) < 0 := lt_of_not_ge hl
    have hLneg : P.L (n : Real) < 0 := by
      unfold Zeta23.Params.L
      exact mul_neg_of_pos_of_neg hP.lam_pos hlneg
    linarith

/-- Therefore a Claude-compatible Weil test at T=n cannot be nonzero anywhere
strictly inside the positive logarithmic Legendre window.  This is a direct
support statement, not a claim that every possible use of pair correlation is
impossible. -/
theorem zeta23_valid_weilTest_zero_inside_legendre_window
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n)
    (f g : Real → Complex)
    (hfs : tsupport f ⊆ Icc (-(P.L (n : Real) / 2)) (P.L (n : Real) / 2))
    (hgs : tsupport g ⊆ Icc (-(P.L (n : Real) / 2)) (P.L (n : Real) / 2))
    {x : Real} (hx : emeraldLogLeft n < x) :
    Zeta23.EF.weilTest f g x = 0 := by
  exact weilTest_eq_zero_of_support_right hfs hgs
    (lt_trans (zeta23_valid_L_at_n_lt_emeraldLogLeft P hP n hn) hx)

end
end KernelEsmeralda
