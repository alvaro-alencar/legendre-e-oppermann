import Mathlib.Topology.Algebra.InfiniteSum.Basic
import KernelEsmeralda.WeilInterface

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

theorem emeraldWeilTest_neg_log_eq_zero
    (K : Real → Real) (n m : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilTest K (-Real.log (m : Real)) = 0 := by
  have hnR : (2 : Real) ≤ n := by
    exact_mod_cast hn
  have hleftpos : 0 < emeraldLogLeft n := by
    unfold emeraldLogLeft lowerSquare
    apply Real.log_pos
    nlinarith
  have hlog : 0 ≤ Real.log (m : Real) := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · apply Real.log_nonneg
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 hm0)
  have hneg : -Real.log (m : Real) < emeraldLogLeft n :=
    lt_of_le_of_lt (neg_nonpos.mpr hlog) hleftpos
  have hKneg : K (-Real.log (m : Real)) = 0 := by
    by_contra hne
    have hs : -Real.log (m : Real) ∈ Function.support K := hne
    have hi := hsupp hs
    exact (lt_asymm hi.1 hneg)
  simp [emeraldWeilTest, emeraldTilt, hKneg]

def emeraldWeilWindowPrimeSum (K : Real → Real) (n : Nat) : Complex :=
  ∑ m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2),
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt (m : Real) : Real) : Complex) *
      (emeraldWeilTest K (Real.log (m : Real)) +
        emeraldWeilTest K (-Real.log (m : Real)))

theorem emeraldWeilWindowPrimeSum_eq_mass_sum
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilWindowPrimeSum K n =
      ∑ m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2),
        ((ArithmeticFunction.vonMangoldt m * K (Real.log (m : Real)) : Real) : Complex) := by
  unfold emeraldWeilWindowPrimeSum
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m :=
    lt_of_le_of_lt (Nat.zero_le (n ^ 2)) (Finset.mem_Ioc.mp hm).1
  rw [emeraldWeilTest_neg_log_eq_zero K n m hn hsupp, add_zero]
  exact weil_prime_factor_normalization_complex K m hmpos

theorem emeraldWeilWindowPrimeSum_eq_emeraldMass
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilWindowPrimeSum K n = (emeraldMass K n : Complex) := by
  rw [emeraldWeilWindowPrimeSum_eq_mass_sum K n hn hsupp]
  simp [emeraldMass]

theorem mem_square_window_of_emerald_log_ne_zero
    (K : Real → Real) (n m : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hK : K (Real.log (m : Real)) ≠ 0) :
    m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2) := by
  have hs : Real.log (m : Real) ∈ Function.support K := hK
  have hi := hsupp hs
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  have hnpos : (0 : Real) < n := by exact_mod_cast hnposNat
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hsquares : lowerSquare n < upperSquare n := by
    unfold lowerSquare upperSquare
    have hsucc : (n : Real) < (((n + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.lt_succ_self n
    nlinarith
  have hupos : 0 < upperSquare n := hlpos.trans hsquares
  have hleftlog : 0 < emeraldLogLeft n := by
    unfold emeraldLogLeft
    apply Real.log_pos
    unfold lowerSquare
    have hnat : 1 < n ^ 2 := by
      exact lt_of_lt_of_le (by norm_num : 1 < 2 ^ 2) (Nat.pow_le_pow_left hn 2)
    exact_mod_cast hnat
  have hlogpos : 0 < Real.log (m : Real) := hleftlog.trans hi.1
  have hmgt1 : (1 : Real) < m :=
    (Real.log_pos_iff (Nat.cast_nonneg m)).1 hlogpos
  have hmpos : (0 : Real) < m := zero_lt_one.trans hmgt1
  have hloR : lowerSquare n < (m : Real) :=
    (Real.log_lt_log_iff hlpos hmpos).1 hi.1
  have hupR : (m : Real) < upperSquare n :=
    (Real.log_lt_log_iff hmpos hupos).1 hi.2
  rw [Finset.mem_Ioc]
  constructor
  · unfold lowerSquare at hloR
    exact_mod_cast hloR
  · unfold upperSquare at hupR
    have hupNat : m < (n + 1) ^ 2 := by
      exact_mod_cast hupR
    exact hupNat.le

def emeraldWeilPrimeTerm (K : Real → Real) (m : Nat) : Complex :=
  ((ArithmeticFunction.vonMangoldt m / Real.sqrt (m : Real) : Real) : Complex) *
    (emeraldWeilTest K (Real.log (m : Real)) +
      emeraldWeilTest K (-Real.log (m : Real)))

theorem emeraldWeilPrimeTerm_eq_zero_of_not_mem_window
    (K : Real → Real) (n m : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hm : m ∉ Finset.Ioc (n ^ 2) ((n + 1) ^ 2)) :
    emeraldWeilPrimeTerm K m = 0 := by
  have hK : K (Real.log (m : Real)) = 0 := by
    by_contra hne
    exact hm (mem_square_window_of_emerald_log_ne_zero K n m hn hsupp hne)
  have hpos : emeraldWeilTest K (Real.log (m : Real)) = 0 := by
    simp [emeraldWeilTest, emeraldTilt, hK]
  have hneg := emeraldWeilTest_neg_log_eq_zero K n m hn hsupp
  simp [emeraldWeilPrimeTerm, hpos, hneg]

def emeraldWeilPrimeSide (K : Real → Real) : Complex :=
  ∑' m : Nat, emeraldWeilPrimeTerm K m

theorem emeraldWeilPrimeSide_eq_window
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilPrimeSide K = emeraldWeilWindowPrimeSum K n := by
  unfold emeraldWeilPrimeSide emeraldWeilWindowPrimeSum
  apply HasSum.tsum_eq
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  exact emeraldWeilPrimeTerm_eq_zero_of_not_mem_window K n m hn hsupp hm

theorem emeraldWeilPrimeSide_eq_emeraldMass
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilPrimeSide K = (emeraldMass K n : Complex) := by
  rw [emeraldWeilPrimeSide_eq_window K n hn hsupp]
  exact emeraldWeilWindowPrimeSum_eq_emeraldMass K n hn hsupp

end
end KernelEsmeralda
