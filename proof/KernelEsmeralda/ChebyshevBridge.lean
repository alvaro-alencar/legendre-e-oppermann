import Mathlib.NumberTheory.Chebyshev

namespace KernelEsmeralda

noncomputable section

/-- Extremidade inferior do intervalo de Legendre, vista em `ℝ`. -/
def lowerSquare (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- Extremidade superior do intervalo de Legendre, vista em `ℝ`. -/
def upperSquare (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) ^ 2

/-- Incremento real da função de Chebyshev `ψ` no intervalo quadrático. -/
def deltaPsi (n : ℕ) : ℝ :=
  Chebyshev.psi (upperSquare n) - Chebyshev.psi (lowerSquare n)

/-- Incremento real da função de Chebyshev `θ` no mesmo intervalo. -/
def deltaTheta (n : ℕ) : ℝ :=
  Chebyshev.theta (upperSquare n) - Chebyshev.theta (lowerSquare n)

/-- Parte de `ψ` que não é explicada por `θ`.

Em termos aritméticos, esta é precisamente a massa proveniente das potências de primos
além da primeira potência.
-/
def higherPowerRemainder (x : ℝ) : ℝ :=
  Chebyshev.psi x - Chebyshev.theta x

/-- A decomposição de janela é uma identidade algébrica exata:

`Δψ = Δθ + Δ(ψ - θ)`.

Este é o elo formal entre a diferença real de `ψ` e a massa que pode ser atribuída aos
primos (`Δθ`) versus às potências superiores.
-/
theorem deltaPsi_eq_deltaTheta_add_remainderDelta (n : ℕ) :
    deltaPsi n =
      deltaTheta n +
        (higherPowerRemainder (upperSquare n) -
          higherPowerRemainder (lowerSquare n)) := by
  simp [deltaPsi, deltaTheta, higherPowerRemainder]
  ring

/-- A parte de potências superiores é não-negativa. -/
theorem higherPowerRemainder_nonneg (x : ℝ) :
    0 ≤ higherPowerRemainder x := by
  exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)

/-- Mathlib já fornece uma cota global `O(√x)` para `ψ(x) - θ(x)`.

Mantemos a constante existencial exatamente como no teorema da biblioteca.
-/
theorem exists_sqrt_remainder_bound :
    ∃ C : ℝ, ∀ x : ℝ,
      higherPowerRemainder x ≤ C * Real.sqrt x := by
  simpa [higherPowerRemainder] using Chebyshev.psi_sub_theta_le_mul_sqrt

/-- Uma cota global para `ψ - θ` no extremo superior também controla a variação da
parte de potências superiores dentro da janela, porque o valor no extremo inferior é
não-negativo.
-/
theorem remainderDelta_le_upperBound
    {C : ℝ}
    (hC : ∀ x : ℝ, higherPowerRemainder x ≤ C * Real.sqrt x)
    (n : ℕ) :
    higherPowerRemainder (upperSquare n) -
        higherPowerRemainder (lowerSquare n)
      ≤ C * Real.sqrt (upperSquare n) := by
  have hl := higherPowerRemainder_nonneg (lowerSquare n)
  have hu := hC (upperSquare n)
  linarith

/-- Se `Δψ` domina a variação da contribuição das potências superiores, então a massa
puramente prima `Δθ` é positiva.
-/
theorem deltaTheta_pos_of_deltaPsi_gt_remainderDelta
    (n : ℕ)
    (hdom :
      higherPowerRemainder (upperSquare n) -
          higherPowerRemainder (lowerSquare n) < deltaPsi n) :
    0 < deltaTheta n := by
  have hsplit := deltaPsi_eq_deltaTheta_add_remainderDelta n
  linarith

/-- Versão suficiente usando qualquer cota global do tipo `ψ - θ ≤ C√x`.

Este teorema é útil como "barreira": para provar Legendre por esta rota, é necessário
obter para `Δψ` uma cota que ultrapasse o custo de controlar as potências superiores.
-/
theorem deltaTheta_pos_of_deltaPsi_gt_sqrtBound
    {C : ℝ}
    (hC : ∀ x : ℝ, higherPowerRemainder x ≤ C * Real.sqrt x)
    (n : ℕ)
    (hdom : C * Real.sqrt (upperSquare n) < deltaPsi n) :
    0 < deltaTheta n := by
  have hrem := remainderDelta_le_upperBound hC n
  apply deltaTheta_pos_of_deltaPsi_gt_remainderDelta n
  linarith

end

end KernelEsmeralda
