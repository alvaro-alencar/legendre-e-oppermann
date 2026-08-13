import KernelEsmeralda.ChebyshevBridge
import KernelEsmeralda.PrimeFromThetaCore

namespace KernelEsmeralda

noncomputable section

/-- Critério exato: se o incremento de `ψ` domina a variação da parte
`ψ - θ`, então existe um primo entre quadrados consecutivos. -/
theorem legendre_of_deltaPsi_gt_remainderDelta
    (n : ℕ)
    (hdom :
      higherPowerRemainder (upperSquare n) -
          higherPowerRemainder (lowerSquare n) < deltaPsi n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply exists_prime_between_squares_of_deltaTheta_pos n
  exact deltaTheta_pos_of_deltaPsi_gt_remainderDelta n hdom

/-- Critério suficiente usando qualquer cota global
`ψ(x) - θ(x) ≤ C √x`. -/
theorem legendre_of_deltaPsi_gt_sqrtBound
    {C : ℝ}
    (hC : ∀ x : ℝ, higherPowerRemainder x ≤ C * Real.sqrt x)
    (n : ℕ)
    (hdom : C * Real.sqrt (upperSquare n) < deltaPsi n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply exists_prime_between_squares_of_deltaTheta_pos n
  exact deltaTheta_pos_of_deltaPsi_gt_sqrtBound hC n hdom

/-- Mathlib já fornece uma constante global `C` para a cota `O(√x)`.
Consequentemente existe uma constante fixa para a qual a desigualdade
`C√((n+1)²) < Δψ(n)` é uma condição suficiente para Legendre. -/
theorem exists_global_sqrt_legendre_criterion :
    ∃ C : ℝ, ∀ n : ℕ,
      C * Real.sqrt (upperSquare n) < deltaPsi n →
        ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_sqrt_remainder_bound
  refine ⟨C, ?_⟩
  intro n hdom
  exact legendre_of_deltaPsi_gt_sqrtBound hC n hdom

end

end KernelEsmeralda
