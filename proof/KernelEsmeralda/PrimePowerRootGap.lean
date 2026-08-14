import Mathlib.Analysis.MeanInequalitiesPow
import KernelEsmeralda.PrimePowerExact

namespace KernelEsmeralda

noncomputable section

private theorem square_rpow_inv_nat_eq
    (a : Real) (ha : 0 ≤ a) (k : Nat) :
    (a ^ (2 : Nat)) ^ ((1 : Real) / k) =
      a ^ ((2 : Real) / k) := by
  rw [← Real.rpow_natCast]
  rw [Real.rpow_mul ha]
  congr 1
  ring

theorem primePowerRootWindow_le_one
    (n k : Nat) (hk : 2 ≤ k) :
    upperSquare n ^ ((1 : Real) / k) ≤
      lowerSquare n ^ ((1 : Real) / k) + 1 := by
  have hkR : (2 : Real) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : Real) < k := lt_of_lt_of_le (by norm_num) hkR
  have hp0 : (0 : Real) ≤ (2 : Real) / k := by positivity
  have hp1 : (2 : Real) / k ≤ 1 := by
    exact (div_le_one hkpos).2 hkR
  have hsub := Real.rpow_add_le_add_rpow
    (a := (n : Real)) (b := 1) (by positivity) (by norm_num) hp0 hp1
  have hn0 : (0 : Real) ≤ n := by positivity
  have hs0 : (0 : Real) ≤ ((n + 1 : Nat) : Real) := by positivity
  unfold lowerSquare upperSquare
  rw [square_rpow_inv_nat_eq _ hs0, square_rpow_inv_nat_eq _ hn0]
  norm_num at hsub ⊢
  exact hsub

end
end KernelEsmeralda
