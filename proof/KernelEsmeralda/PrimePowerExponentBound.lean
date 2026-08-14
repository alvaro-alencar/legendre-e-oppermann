import KernelEsmeralda.PrimePowerRootGap
import KernelEsmeralda.ThetaShortInterval

namespace KernelEsmeralda

noncomputable section

theorem primePowerExponent_thetaDiff_le_log_upper
    (n k : Nat) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    Chebyshev.theta (upperSquare n ^ ((1 : Real) / k)) -
        Chebyshev.theta (lowerSquare n ^ ((1 : Real) / k)) ≤
      Real.log (upperSquare n) := by
  let x : Real := lowerSquare n ^ ((1 : Real) / k)
  let y : Real := upperSquare n ^ ((1 : Real) / k)
  have hkpos : (0 : Real) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hp0 : (0 : Real) ≤ (1 : Real) / k := by positivity
  have hp1 : (1 : Real) / k ≤ 1 := by
    exact (div_le_one hkpos).2 (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hk))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by positivity) _
  have hu1 : (1 : Real) ≤ upperSquare n := by
    have hnr : (2 : Real) ≤ n := by exact_mod_cast hn
    unfold upperSquare
    nlinarith [sq_nonneg (((n + 1 : Nat) : Real) - 1)]
  have hy1 : 1 ≤ y := by
    dsimp [y]
    exact Real.one_le_rpow hu1 hp0
  have hgap : y ≤ x + 1 := by
    simpa [x, y] using primePowerRootWindow_le_one n k hk
  have hfloor : ⌊y⌋₊ ≤ ⌊x⌋₊ + 1 := by
    have hf : ⌊y⌋₊ ≤ ⌊x + 1⌋₊ := Nat.floor_mono hgap
    rw [Nat.floor_add_one hx0] at hf
    exact hf
  have htheta := theta_sub_le_log_of_floor_le_succ hx0 hy1 hfloor
  have hyu : y ≤ upperSquare n := by
    dsimp [y]
    exact Real.rpow_le_self_of_one_le hu1 hp1
  have hlog : Real.log y ≤ Real.log (upperSquare n) := by
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hy1) hyu
  exact htheta.trans hlog

end
end KernelEsmeralda
