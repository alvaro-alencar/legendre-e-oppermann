import KernelEsmeralda.CriticalLineFrequency

namespace KernelEsmeralda

noncomputable section

/-- The translation center is exactly the logarithm of the geometric location
n(n+1) between the consecutive squares. -/
theorem emeraldTaperCenter_eq_log_product
    (n : Nat) (hn : 1 ≤ n) :
    emeraldTaperCenter n =
      Real.log ((n : Real) * (((n + 1 : Nat) : Real))) := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  rw [emeraldTaperCenter_eq_log_add_log n hn]
  rw [Real.log_mul hnpos.ne' hspos.ne']

/-- Exponentiating the center gives the exact transition height n(n+1). -/
theorem exp_emeraldTaperCenter_eq_product
    (n : Nat) (hn : 1 ≤ n) :
    Real.exp (emeraldTaperCenter n) =
      (n : Real) * (((n + 1 : Nat) : Real)) := by
  have hnpos : (0 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  rw [emeraldTaperCenter_eq_log_product n hn]
  exact Real.exp_log (mul_pos hnpos hspos)

/-- At the exact height T = n(n+1), the normalized translation frequency is 1.
This is the bandwidth-one transition for the Emerald phase. -/
theorem emeraldNormalizedFrequency_eq_one_at_product_height
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n /
        Real.log ((n : Real) * (((n + 1 : Nat) : Real))) = 1 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnR : (1 : Real) < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hsR : (1 : Real) < (((n + 1 : Nat) : Real)) := by
    exact_mod_cast (lt_trans Nat.one_lt_two (Nat.lt_succ_of_le hn))
  have hprod : (1 : Real) <
      (n : Real) * (((n + 1 : Nat) : Real)) := by nlinarith
  have hlogne : Real.log ((n : Real) * (((n + 1 : Nat) : Real))) ≠ 0 :=
    (Real.log_pos hprod).ne'
  rw [emeraldTaperCenter_eq_log_product n hn1]
  exact div_self hlogne

/-- The square-height endpoint already lies on the low-frequency side:
the Emerald center is strictly smaller than log((n+1)^2). -/
theorem emeraldNormalizedFrequency_lt_one_at_upperSquare
    (n : Nat) (hn : 2 ≤ n) :
    emeraldTaperCenter n / Real.log (upperSquare n) < 1 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hchain := emeraldLinearCore_chain n hn1
  have hleftRight : emeraldLogLeft n < emeraldLogRight n := by
    exact lt_trans hchain.1 (lt_trans hchain.2.1 hchain.2.2)
  have hcenterlt : emeraldTaperCenter n < emeraldLogRight n := by
    unfold emeraldTaperCenter
    linarith
  have hsR : (1 : Real) < (((n + 1 : Nat) : Real)) := by
    exact_mod_cast (lt_trans Nat.one_lt_two (Nat.lt_succ_of_le hn))
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) :=
    lt_trans zero_lt_one hsR
  have hsSq :
      (((n + 1 : Nat) : Real)) <
        (((n + 1 : Nat) : Real)) * (((n + 1 : Nat) : Real)) := by
    simpa using mul_lt_mul_of_pos_left hsR hspos
  have hu : (1 : Real) < upperSquare n := by
    unfold upperSquare
    rw [pow_two]
    exact lt_trans hsR hsSq
  have hlogpos : 0 < Real.log (upperSquare n) := Real.log_pos hu
  unfold emeraldLogRight at hcenterlt
  rw [div_lt_iff₀ hlogpos]
  simpa using hcenterlt

end
end KernelEsmeralda
