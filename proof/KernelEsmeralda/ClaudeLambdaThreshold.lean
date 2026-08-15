import KernelEsmeralda.ClaudeFixedLambdaBarrier

namespace KernelEsmeralda

noncomputable section

/-- At square spectral scale `T = 2π (n+1)^2`, this is the exact normalized
bandwidth needed for a Zeta23 support interval to reach the left endpoint
`log(n^2)` of the Legendre window. -/
def emeraldClaudeLambdaMin (n : Nat) : Real :=
  emeraldLogLeft n / emeraldLogRight n

private theorem emeraldLogRight_pos_of_two
    (n : Nat) (hn : 2 ≤ n) :
    0 < emeraldLogRight n := by
  have hs : (1 : Real) < upperSquare n := by
    unfold upperSquare
    have hsucc : (2 : Real) ≤ (((n + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_le_succ (le_trans (by decide : 1 ≤ 2) hn)
    nlinarith
  unfold emeraldLogRight
  exact Real.log_pos hs

private theorem emeraldLogLeft_pos_of_two
    (n : Nat) (hn : 2 ≤ n) :
    0 < emeraldLogLeft n := by
  have hs : (1 : Real) < lowerSquare n := by
    unfold lowerSquare
    have hnR : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
    nlinarith
  unfold emeraldLogLeft
  exact Real.log_pos hs

private theorem emeraldLogLeft_lt_right_of_two
    (n : Nat) (hn : 2 ≤ n) :
    emeraldLogLeft n < emeraldLogRight n := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have h := emeraldLinearCore_chain n hn1
  exact lt_trans h.1 (lt_trans h.2.1 h.2.2)

theorem emeraldClaudeLambdaMin_pos
    (n : Nat) (hn : 2 ≤ n) :
    0 < emeraldClaudeLambdaMin n := by
  unfold emeraldClaudeLambdaMin
  exact div_pos (emeraldLogLeft_pos_of_two n hn)
    (emeraldLogRight_pos_of_two n hn)

theorem emeraldClaudeLambdaMin_lt_one
    (n : Nat) (hn : 2 ≤ n) :
    emeraldClaudeLambdaMin n < 1 := by
  unfold emeraldClaudeLambdaMin
  rw [div_lt_one (emeraldLogRight_pos_of_two n hn)]
  exact emeraldLogLeft_lt_right_of_two n hn

/-- Exact reach criterion.  At `T = 2π (n+1)^2`, a Zeta23 parameter reaches
`log(n^2)` iff its bandwidth parameter is at least `λ_min(n)`. -/
theorem zeta23_square_scale_reaches_left_iff
    (P : Zeta23.Params) (n : Nat) (hn : 2 ≤ n) :
    emeraldLogLeft n ≤ P.L (2 * Real.pi * upperSquare n) ↔
      emeraldClaudeLambdaMin n ≤ P.lam := by
  rw [zeta23_L_at_two_pi_upperSquare]
  unfold emeraldClaudeLambdaMin
  have hR := emeraldLogRight_pos_of_two n hn
  rw [div_le_iff₀ hR]
  exact Iff.rfl

/-- The distance from the endpoint bandwidth `1` is exactly the Legendre
logarithmic window length divided by its right endpoint. -/
theorem one_sub_emeraldClaudeLambdaMin
    (n : Nat) (hn : 2 ≤ n) :
    1 - emeraldClaudeLambdaMin n =
      emeraldTaperLength n / emeraldLogRight n := by
  have hRne := (emeraldLogRight_pos_of_two n hn).ne'
  unfold emeraldClaudeLambdaMin emeraldTaperLength
  field_simp [hRne]
  ring

/-- Quantitative squeeze: the bandwidth deficit is at most the elementary
window-length bound `2/n`, divided by the positive right logarithmic endpoint. -/
theorem one_sub_emeraldClaudeLambdaMin_le
    (n : Nat) (hn : 2 ≤ n) :
    1 - emeraldClaudeLambdaMin n ≤
      (2 / (n : Real)) / emeraldLogRight n := by
  rw [one_sub_emeraldClaudeLambdaMin n hn]
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hlen := emeraldTaperLength_le_two_div_n n hn1
  exact div_le_div_of_nonneg_right hlen (emeraldLogRight_pos_of_two n hn).le

/-- A completely explicit, slightly weaker version.  Since
`log((n+1)^2) ≥ log 4`, the required bandwidth satisfies
`λ_min(n) ≥ 1 - 2/(n log 4)`. -/
theorem emeraldClaudeLambdaMin_ge_one_sub_explicit
    (n : Nat) (hn : 2 ≤ n) :
    1 - 2 / ((n : Real) * Real.log 4) ≤ emeraldClaudeLambdaMin n := by
  have hnR : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hR := emeraldLogRight_pos_of_two n hn
  have hR4 : Real.log 4 ≤ emeraldLogRight n := by
    have h4 : (4 : Real) ≤ upperSquare n := by
      unfold upperSquare
      have hsucc : (2 : Real) ≤ (((n + 1 : Nat) : Real)) := by
        exact_mod_cast Nat.succ_le_succ (le_trans (by decide : 1 ≤ 2) hn)
      nlinarith
    unfold emeraldLogRight
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (lt_of_lt_of_le (by norm_num) h4) h4
  have hdef := one_sub_emeraldClaudeLambdaMin_le n hn
  have hden :
      (2 / (n : Real)) / emeraldLogRight n ≤
        2 / ((n : Real) * Real.log 4) := by
    have hnnonneg : 0 ≤ (2 / (n : Real)) := by positivity
    have hinv : 1 / emeraldLogRight n ≤ 1 / Real.log 4 :=
      one_div_le_one_div_of_le hlog4 hR4
    calc
      (2 / (n : Real)) / emeraldLogRight n
          = (2 / (n : Real)) * (1 / emeraldLogRight n) := by ring
      _ ≤ (2 / (n : Real)) * (1 / Real.log 4) :=
        mul_le_mul_of_nonneg_left hinv hnnonneg
      _ = 2 / ((n : Real) * Real.log 4) := by
        field_simp [hnR.ne', hlog4.ne']
  linarith

end
end KernelEsmeralda
