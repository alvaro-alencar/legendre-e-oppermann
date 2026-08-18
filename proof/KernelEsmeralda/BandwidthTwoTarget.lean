import KernelEsmeralda.CriticalLineFrequency

namespace KernelEsmeralda

noncomputable section

/-- The natural normalized frequency is exactly `2` plus the logarithmic
increment from `n` to `n+1`. -/
theorem emeraldNaturalFrequency_eq_two_add_log_ratio
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n / Real.log (n : Real) =
      2 + Real.log ((((n + 1 : Nat) : Real)) / (n : Real)) /
        Real.log (n : Real) := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  have hlogn : Real.log (n : Real) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))).ne'
  rw [emeraldTaperCenter_eq_log_add_log n hn1]
  have hdiv := Real.log_div hspos.ne' hnpos.ne'
  field_simp [hlogn]
  rw [hdiv]
  ring

/-- The excess beyond bandwidth two is exactly the tiny ratio
`log(1+1/n)/log n`. -/
theorem emeraldNaturalFrequency_sub_two
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n / Real.log (n : Real) - 2 =
      Real.log ((((n + 1 : Nat) : Real)) / (n : Real)) /
        Real.log (n : Real) := by
  rw [emeraldNaturalFrequency_eq_two_add_log_ratio n hn]
  ring

/-- Elementary upper bound for the excess over bandwidth two. -/
theorem emeraldNaturalFrequency_sub_two_le
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n / Real.log (n : Real) - 2 ≤
      1 / ((n : Real) * Real.log (n : Real)) := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  have hlogpos : 0 < Real.log (n : Real) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))
  rw [emeraldNaturalFrequency_sub_two n hn]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hspos hnpos)
  have hratio :
      (((n + 1 : Nat) : Real)) / (n : Real) - 1 = 1 / (n : Real) := by
    push_cast
    field_simp [hnpos.ne']
    ring
  rw [hratio] at hlog
  have hdiv :
      Real.log ((((n + 1 : Nat) : Real)) / (n : Real)) /
          Real.log (n : Real) ≤
        (1 / (n : Real)) / Real.log (n : Real) :=
    div_le_div_of_nonneg_right hlog hlogpos.le
  calc
    Real.log ((((n + 1 : Nat) : Real)) / (n : Real)) /
        Real.log (n : Real)
        ≤ (1 / (n : Real)) / Real.log (n : Real) := hdiv
    _ = 1 / ((n : Real) * Real.log (n : Real)) := by
      field_simp [hnpos.ne', hlogpos.ne']

/-- The natural Legendre frequency actually lies in the narrow interval
`(2,3)` for every `n ≥ 2`. -/
theorem emeraldNaturalFrequency_lt_three
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n / Real.log (n : Real) < 3 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnR : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hnpos : (0 : Real) < (n : Real) := lt_of_lt_of_le (by norm_num) hnR
  have hlogpos : 0 < Real.log (n : Real) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hnR)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  have hsq : (((n + 1 : Nat) : Real)) < (n : Real) ^ 2 := by
    push_cast
    nlinarith
  have hlogsq :
      Real.log (((n + 1 : Nat) : Real)) < Real.log ((n : Real) ^ 2) :=
    Real.strictMonoOn_log hspos (sq_pos_of_pos hnpos) hsq
  have hlogpow : Real.log ((n : Real) ^ 2) = 2 * Real.log (n : Real) := by
    rw [show (n : Real) ^ 2 = (n : Real) * (n : Real) by ring]
    rw [Real.log_mul hnpos.ne' hnpos.ne']
    ring
  rw [hlogpow] at hlogsq
  rw [emeraldTaperCenter_eq_log_add_log n hn1]
  rw [div_lt_iff₀ hlogpos]
  linarith

/-- Any hypothetical correlation theorem with a fixed bandwidth `α > 2`
would geometrically cover the natural Legendre phase as soon as the explicit
excess bound is smaller than `α-2`.  This is a geometry statement only; it
does not provide such a correlation theorem. -/
theorem emeraldNaturalFrequency_lt_of_bandwidth_gt_two
    (alpha : Real) (n : Nat) (hn : 2 ≤ n)
    (hband : 1 / ((n : Real) * Real.log (n : Real)) < alpha - 2) :
    emeraldTaperCenter n / Real.log (n : Real) < alpha := by
  have h := emeraldNaturalFrequency_sub_two_le n hn
  linarith

end
end KernelEsmeralda
