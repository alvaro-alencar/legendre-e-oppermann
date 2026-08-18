import KernelEsmeralda.ChebyshevBridge

namespace KernelEsmeralda

noncomputable section

theorem exists_prime_between_squares_of_deltaTheta_pos
    (n : ℕ) (hpos : 0 < deltaTheta n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  by_contra hno
  have hsets : Nat.primesLE ((n + 1) ^ 2) = Nat.primesLE (n ^ 2) := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hpu, hp⟩
      refine ⟨?_, hp⟩
      by_contra hnle
      have hlp : n ^ 2 < p := Nat.lt_of_not_ge hnle
      have hnp : ¬ Nat.Prime ((n + 1) ^ 2) :=
        Nat.Prime.not_prime_pow (x := n + 1) (n := 2) (by norm_num)
      have hneq : p ≠ (n + 1) ^ 2 := by
        intro heq
        subst p
        exact hnp hp
      have hplt : p < (n + 1) ^ 2 := by omega
      exact False.elim (hno ⟨p, hp, hlp, hplt⟩)
    · rintro ⟨hpl, hp⟩
      refine ⟨?_, hp⟩
      exact hpl.trans (Nat.pow_le_pow_left (Nat.le_succ n) 2)
  have htheta :
      Chebyshev.theta (((n + 1) ^ 2 : ℕ) : ℝ) =
        Chebyshev.theta ((n ^ 2 : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,
      Chebyshev.theta_eq_sum_primesLE_log, hsets]
  have hpos' :
      0 < Chebyshev.theta (((n + 1) ^ 2 : ℕ) : ℝ) -
        Chebyshev.theta ((n ^ 2 : ℕ) : ℝ) := by
    simpa [deltaTheta, upperSquare, lowerSquare] using hpos
  rw [htheta] at hpos'
  linarith

end
end KernelEsmeralda
