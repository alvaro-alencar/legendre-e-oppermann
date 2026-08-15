import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import KernelEsmeralda.CriticalLineTaperBound

namespace KernelEsmeralda

noncomputable section

theorem exp_emeraldLogRight_half_eq_succ (n : Nat) :
    Real.exp (emeraldLogRight n / 2) = (((n + 1 : Nat) : Real)) := by
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  have hsqpos : (0 : Real) < (((n + 1 : Nat) : Real)) ^ 2 := by positivity
  unfold emeraldLogRight upperSquare
  calc
    Real.exp (Real.log ((((n + 1 : Nat) : Real)) ^ 2) / 2)
        = Real.sqrt ((((n + 1 : Nat) : Real)) ^ 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hsqpos]
          congr 1
          ring
    _ = (((n + 1 : Nat) : Real)) := by
          rw [Real.sqrt_sq hspos.le]

theorem emeraldTaperLength_eq_two_mul_log_ratio
    (n : Nat) (hn : 1 ≤ n) :
    emeraldTaperLength n =
      2 * Real.log ((((n + 1 : Nat) : Real)) / (n : Real)) := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  unfold emeraldTaperLength emeraldLogRight emeraldLogLeft upperSquare lowerSquare
  rw [show (((n + 1 : Nat) : Real)) ^ 2 =
      (((n + 1 : Nat) : Real)) * (((n + 1 : Nat) : Real)) by ring]
  rw [show ((n : Real) ^ 2) = (n : Real) * (n : Real) by ring]
  rw [Real.log_mul hspos.ne' hspos.ne', Real.log_mul hnpos.ne' hnpos.ne']
  rw [Real.log_div hspos.ne' hnpos.ne']
  ring

theorem emeraldTaperLength_le_two_div_n
    (n : Nat) (hn : 1 ≤ n) :
    emeraldTaperLength n ≤ 2 / (n : Real) := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : Real) < (((n + 1 : Nat) : Real)) := by positivity
  rw [emeraldTaperLength_eq_two_mul_log_ratio n hn]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hspos hnpos)
  have hratio : (((n + 1 : Nat) : Real)) / (n : Real) - 1 = 1 / (n : Real) := by
    push_cast
    field_simp [hnpos.ne']
    ring
  rw [hratio] at hlog
  calc
    2 * Real.log ((((n + 1 : Nat) : Real)) / (n : Real))
        ≤ 2 * (1 / (n : Real)) := by nlinarith [hlog]
    _ = 2 / (n : Real) := by ring

theorem criticalLineGeometricFactor_le_four
    (n : Nat) (hn : 1 ≤ n) :
    Real.exp (emeraldLogRight n / 2) * emeraldTaperLength n ≤ 4 := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnR : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hlen := emeraldTaperLength_le_two_div_n n hn
  have hsucc0 : (0 : Real) ≤ (((n + 1 : Nat) : Real)) := by positivity
  rw [exp_emeraldLogRight_half_eq_succ]
  calc
    (((n + 1 : Nat) : Real)) * emeraldTaperLength n
        ≤ (((n + 1 : Nat) : Real)) * (2 / (n : Real)) :=
          mul_le_mul_of_nonneg_left hlen hsucc0
    _ = 2 * (((n + 1 : Nat) : Real)) / (n : Real) := by ring
    _ ≤ 4 := by
      rw [div_le_iff₀ hnpos]
      push_cast
      nlinarith [hnR]

theorem emerald_zero_kernel_factor_bound_four_on_critical_line
    (n : Nat) (hn : 1 ≤ n) (rho : Zeta23.zetaZeroConfig.carrier)
    (hrho : (rho : Complex).re = 1 / 2) :
    ‖Complex.exp ((rho : Complex) * (emeraldTaperCenter n : Complex)) *
        Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
          (emeraldTaperLength n) (emeraldTaperWidth n)
          (-Complex.I * (rho : Complex))‖ ≤ 4 := by
  exact (emerald_zero_kernel_factor_bound_on_critical_line n hn rho hrho).trans
    (criticalLineGeometricFactor_le_four n hn)

end
end KernelEsmeralda
