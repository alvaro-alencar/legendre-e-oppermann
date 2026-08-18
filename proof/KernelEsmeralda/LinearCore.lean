import KernelEsmeralda.PoleInterval

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

def emeraldLinearCoreLeftX (n : Nat) : Real :=
  lowerSquare n + (n : Real) / 2

def emeraldLinearCoreRightX (n : Nat) : Real :=
  lowerSquare n + 3 * (n : Real) / 2

def emeraldLinearCoreLeft (n : Nat) : Real :=
  Real.log (emeraldLinearCoreLeftX n)

def emeraldLinearCoreRight (n : Nat) : Real :=
  Real.log (emeraldLinearCoreRightX n)

theorem emeraldLinearCore_chain (n : Nat) (hn : 1 ≤ n) :
    emeraldLogLeft n < emeraldLinearCoreLeft n ∧
    emeraldLinearCoreLeft n < emeraldLinearCoreRight n ∧
    emeraldLinearCoreRight n < emeraldLogRight n := by
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < n := by exact_mod_cast hnposNat
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hleftX : lowerSquare n < emeraldLinearCoreLeftX n := by
    unfold emeraldLinearCoreLeftX
    linarith
  have hleftpos : 0 < emeraldLinearCoreLeftX n := hlpos.trans hleftX
  have hcoreX : emeraldLinearCoreLeftX n < emeraldLinearCoreRightX n := by
    unfold emeraldLinearCoreLeftX emeraldLinearCoreRightX
    linarith
  have hrightpos : 0 < emeraldLinearCoreRightX n := hleftpos.trans hcoreX
  have hrightX : emeraldLinearCoreRightX n < upperSquare n := by
    unfold emeraldLinearCoreRightX lowerSquare upperSquare
    norm_num
    nlinarith
  constructor
  · unfold emeraldLogLeft emeraldLinearCoreLeft
    exact Real.log_lt_log hlpos hleftX
  constructor
  · unfold emeraldLinearCoreLeft emeraldLinearCoreRight
    exact Real.log_lt_log hleftpos hcoreX
  · unfold emeraldLinearCoreRight emeraldLogRight
    exact Real.log_lt_log hrightpos hrightX

theorem emeraldLinearCore_exp_sub (n : Nat) (hn : 1 ≤ n) :
    Real.exp (emeraldLinearCoreRight n) - Real.exp (emeraldLinearCoreLeft n) = (n : Real) := by
  have hchain := emeraldLinearCore_chain n hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < n := by exact_mod_cast hnposNat
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hleftX : lowerSquare n < emeraldLinearCoreLeftX n := by
    unfold emeraldLinearCoreLeftX
    linarith
  have hleftpos : 0 < emeraldLinearCoreLeftX n := hlpos.trans hleftX
  have hcoreX : emeraldLinearCoreLeftX n < emeraldLinearCoreRightX n := by
    unfold emeraldLinearCoreLeftX emeraldLinearCoreRightX
    linarith
  have hrightpos : 0 < emeraldLinearCoreRightX n := hleftpos.trans hcoreX
  unfold emeraldLinearCoreLeft emeraldLinearCoreRight
  rw [Real.exp_log hrightpos, Real.exp_log hleftpos]
  unfold emeraldLinearCoreLeftX emeraldLinearCoreRightX
  ring

theorem exists_emerald_minorant_linear_core
    (n : Nat) (hn : 1 ≤ n) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n), K x = 1) ∧
      Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n) := by
  have hchain := emeraldLinearCore_chain n hn
  exact exists_smooth_emerald_minorant hchain.1 hchain.2.2

end
end KernelEsmeralda
