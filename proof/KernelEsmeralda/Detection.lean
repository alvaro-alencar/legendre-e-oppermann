import Mathlib

open scoped BigOperators

namespace KernelEsmeralda

/-- Candidatos primos estritamente entre `n²` e `(n+1)²`. -/
def primesBetweenSquares (n : ℕ) : Finset ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime

/-- Massa logarítmica carregada apenas pelos primos do intervalo de Legendre. -/
def primeMass (n : ℕ) : ℝ :=
  ∑ p in primesBetweenSquares n, Real.log p

/-- Se a massa de primos do intervalo é positiva, então o intervalo contém um primo.

Este lema é deliberadamente elementar: ele separa a etapa lógica de detecção da etapa
analítica difícil, que consiste em obter uma cota positiva para `primeMass n` a partir de
`Δψ` e do Kernel de Esmeralda.
-/
theorem exists_prime_between_squares_of_primeMass_pos
    (n : ℕ) (hpos : 0 < primeMass n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hne : primesBetweenSquares n ≠ ∅ := by
    intro h
    have hz : primeMass n = 0 := by
      simp [primeMass, h]
    linarith
  have hs : (primesBetweenSquares n).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  rcases hs with ⟨p, hp⟩
  have hp' := Finset.mem_filter.mp hp
  have hbounds := Finset.mem_Ioo.mp hp'.1
  exact ⟨p, hp'.2, hbounds.1, hbounds.2⟩

/-- **Lema de Detecção Limpa.**

Suponha que uma quantidade `deltaPsi` tenha sido decomposta exatamente em

`deltaPsi = primeMass n + higherPowerMass`,

onde `higherPowerMass` reúne toda a contribuição das potências de primos `p^k`, `k ≥ 2`.
Se `deltaPsi` é estritamente maior que essa contribuição, então há um primo entre
`n²` e `(n+1)²`.

O teorema NÃO afirma que a decomposição acima já foi provada para a função de Chebyshev.
Essa identificação é o próximo elo formal do projeto.
-/
theorem clean_detection
    (n : ℕ) (deltaPsi higherPowerMass : ℝ)
    (hdecomp : deltaPsi = primeMass n + higherPowerMass)
    (hdominates : higherPowerMass < deltaPsi) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply exists_prime_between_squares_of_primeMass_pos n
  linarith

end KernelEsmeralda
