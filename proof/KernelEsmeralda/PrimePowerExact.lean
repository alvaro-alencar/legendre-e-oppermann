import KernelEsmeralda.ChebyshevBridge

open Finset

namespace KernelEsmeralda

noncomputable section

def higherPowerExponentCutoff (n : Nat) : Nat :=
  ⌊Real.log (upperSquare n) / Real.log 2⌋₊

private theorem lowerSquare_le_upperSquare (n : Nat) :
    lowerSquare n ≤ upperSquare n := by
  have hn0 : (0 : Real) ≤ n := by positivity
  have hs : (n : Real) ≤ ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ n
  unfold lowerSquare upperSquare
  nlinarith [sq_nonneg (((n + 1 : Nat) : Real) - (n : Real))]

theorem lower_exponent_cutoff_le_upper
    (n : Nat) (hn : 1 ≤ n) :
    ⌊Real.log (lowerSquare n) / Real.log 2⌋₊ ≤ higherPowerExponentCutoff n := by
  unfold higherPowerExponentCutoff
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hlu : lowerSquare n ≤ upperSquare n := lowerSquare_le_upperSquare n
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right
  · exact Real.log_le_log hlpos hlu
  · exact (Real.log_pos (by norm_num : (1 : Real) < 2)).le

theorem higherPowerRemainderDelta_eq_exponent_sum
    (n : Nat) (hn : 2 ≤ n) :
    higherPowerRemainder (upperSquare n) -
        higherPowerRemainder (lowerSquare n) =
      ∑ k ∈ Icc 2 (higherPowerExponentCutoff n),
        (Chebyshev.theta (upperSquare n ^ ((1 : Real) / k)) -
          Chebyshev.theta (lowerSquare n ^ ((1 : Real) / k))) := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hnr : (2 : Real) ≤ n := by exact_mod_cast hn
  have hl2 : (2 : Real) ≤ lowerSquare n := by
    unfold lowerSquare
    nlinarith [sq_nonneg ((n : Real) - 2)]
  have hlu : lowerSquare n ≤ upperSquare n := lowerSquare_le_upperSquare n
  have hu2 : (2 : Real) ≤ upperSquare n := hl2.trans hlu
  have hcut := lower_exponent_cutoff_le_upper n hn1
  have hu := Chebyshev.psi_eq_theta_add_sum_theta'
    (x := upperSquare n) hu2 (N := higherPowerExponentCutoff n) (by rfl)
  have hl := Chebyshev.psi_eq_theta_add_sum_theta'
    (x := lowerSquare n) hl2 (N := higherPowerExponentCutoff n) hcut
  unfold higherPowerRemainder
  rw [hu, hl]
  rw [sum_sub_distrib]
  ring

end
end KernelEsmeralda
