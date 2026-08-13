import Mathlib

open scoped BigOperators

namespace KernelEsmeralda

def primesBetweenSquares (n : ℕ) : Finset ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime

noncomputable def primeMass (n : ℕ) : ℝ :=
  ∑ p ∈ primesBetweenSquares n, Real.log p

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

theorem clean_detection
    (n : ℕ) (deltaPsi higherPowerMass : ℝ)
    (hdecomp : deltaPsi = primeMass n + higherPowerMass)
    (hdominates : higherPowerMass < deltaPsi) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply exists_prime_between_squares_of_primeMass_pos n
  linarith

end KernelEsmeralda
