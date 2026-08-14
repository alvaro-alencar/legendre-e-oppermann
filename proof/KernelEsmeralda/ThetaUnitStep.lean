import Mathlib.NumberTheory.Chebyshev

namespace KernelEsmeralda

noncomputable section

theorem theta_nat_succ_sub_le_log (m : Nat) :
    Chebyshev.theta (m + 1 : Nat) - Chebyshev.theta m ≤
      Real.log ((m + 1 : Nat) : Real) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  rw [Nat.primesLE_succ]
  split_ifs with hp
  · rw [Finset.sum_insert (Nat.notMem_primesLE m)]
    ring_nf
  · simp
    exact Real.log_nonneg (by positivity)

end
end KernelEsmeralda
