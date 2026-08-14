import KernelEsmeralda.ThetaUnitStep

namespace KernelEsmeralda

noncomputable section

theorem theta_sub_le_log_of_floor_le_succ
    {x y : Real} (hx0 : 0 ≤ x) (hy1 : 1 ≤ y)
    (hfloor : ⌊y⌋₊ ≤ ⌊x⌋₊ + 1) :
    Chebyshev.theta y - Chebyshev.theta x ≤ Real.log y := by
  rw [Chebyshev.theta_eq_theta_coe_floor y,
    Chebyshev.theta_eq_theta_coe_floor x]
  let a : Nat := ⌊x⌋₊
  let b : Nat := ⌊y⌋₊
  change Chebyshev.theta b - Chebyshev.theta a ≤ Real.log y
  change b ≤ a + 1 at hfloor
  by_cases hba : b ≤ a
  · have htheta : Chebyshev.theta (b : Real) ≤ Chebyshev.theta (a : Real) := by
      exact Chebyshev.theta_mono (by exact_mod_cast hba)
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hy1
    linarith
  · have hab : a < b := Nat.lt_of_not_ge hba
    have hEq : b = a + 1 := by omega
    subst b
    have hstep := theta_nat_succ_sub_le_log a
    have hy0 : 0 ≤ y := le_trans (by norm_num) hy1
    have hfloorY : (((a + 1 : Nat) : Real)) ≤ y := by
      simpa [a] using (Nat.floor_le hy0 : ((⌊y⌋₊ : Nat) : Real) ≤ y)
    have hlogmono : Real.log (((a + 1 : Nat) : Real)) ≤ Real.log y := by
      exact Real.log_le_log (by positivity) hfloorY
    exact hstep.trans hlogmono

end
end KernelEsmeralda
