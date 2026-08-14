import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import KernelEsmeralda.PoleIntegral

open Set
open scoped Interval

namespace KernelEsmeralda

noncomputable section

theorem emeraldCoreLeft_lt_right (n : Nat) (hn : 1 ≤ n) :
    emeraldCoreLeft n < emeraldCoreRight n := by
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < n := by exact_mod_cast hnposNat
  have hsucc : (n : Real) < (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.lt_succ_self n
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hsquares : lowerSquare n < upperSquare n := by
    unfold lowerSquare upperSquare
    nlinarith
  have hlog : emeraldLogLeft n < emeraldLogRight n := by
    unfold emeraldLogLeft emeraldLogRight
    exact Real.log_lt_log hlpos hsquares
  unfold emeraldCoreLeft emeraldCoreRight
  linarith

theorem emeraldCore_exp_weight_integral
    (K : Real → Real) (n : Nat) (hn : 1 ≤ n)
    (hcore : ∀ x ∈ Icc (emeraldCoreLeft n) (emeraldCoreRight n), K x = 1) :
    (∫ u in emeraldCoreLeft n..emeraldCoreRight n, Real.exp u * K u) =
      Real.exp (emeraldCoreRight n) - Real.exp (emeraldCoreLeft n) := by
  have horder : emeraldCoreLeft n ≤ emeraldCoreRight n :=
    (emeraldCoreLeft_lt_right n hn).le
  calc
    (∫ u in emeraldCoreLeft n..emeraldCoreRight n, Real.exp u * K u) =
        ∫ u in emeraldCoreLeft n..emeraldCoreRight n, Real.exp u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le horder] at hu
      change Real.exp u * K u = Real.exp u
      rw [hcore u hu, mul_one]
    _ = Real.exp (emeraldCoreRight n) - Real.exp (emeraldCoreLeft n) := by simp

end
end KernelEsmeralda
