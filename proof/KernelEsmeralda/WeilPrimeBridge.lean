import KernelEsmeralda.WeilInterface

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Para `n ≥ 2`, o suporte do Kernel de Esmeralda fica à direita de zero;
portanto o ramo refletido `k(-log m)` da fórmula de Weil desaparece. -/
theorem emeraldWeilTest_neg_log_eq_zero
    (K : Real → Real) (n m : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilTest K (-Real.log (m : Real)) = 0 := by
  have hnR : (2 : Real) ≤ n := by
    exact_mod_cast hn
  have hleftpos : 0 < emeraldLogLeft n := by
    unfold emeraldLogLeft lowerSquare
    apply Real.log_pos
    nlinarith
  have hlog : 0 ≤ Real.log (m : Real) := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · apply Real.log_nonneg
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 hm0)
  have hneg : -Real.log (m : Real) < emeraldLogLeft n :=
    lt_of_le_of_lt (neg_nonpos.mpr hlog) hleftpos
  have hKneg : K (-Real.log (m : Real)) = 0 := by
    by_contra hne
    have hs : -Real.log (m : Real) ∈ Function.support K := hne
    have hi := hsupp hs
    exact (lt_asymm hi.1 hneg)
  simp [emeraldWeilTest, emeraldTilt, hKneg]

/-- Parte do lado primo de Weil restrita à janela de Legendre. -/
def emeraldWeilWindowPrimeSum (K : Real → Real) (n : Nat) : Complex :=
  ∑ m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2),
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt (m : Real) : Real) : Complex) *
      (emeraldWeilTest K (Real.log (m : Real)) +
        emeraldWeilTest K (-Real.log (m : Real)))

/-- Na janela, o lado primo de Weil coincide termo a termo com a massa esmeralda. -/
theorem emeraldWeilWindowPrimeSum_eq_mass_sum
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilWindowPrimeSum K n =
      ∑ m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2),
        ((ArithmeticFunction.vonMangoldt m * K (Real.log (m : Real)) : Real) : Complex) := by
  unfold emeraldWeilWindowPrimeSum
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m :=
    lt_of_le_of_lt (Nat.zero_le (n ^ 2)) (Finset.mem_Ioc.mp hm).1
  rw [emeraldWeilTest_neg_log_eq_zero K n m hn hsupp, add_zero]
  exact weil_prime_factor_normalization_complex K m hmpos

/-- Em particular, a soma prima de Weil na janela é o `emeraldMass` real embutido em `ℂ`. -/
theorem emeraldWeilWindowPrimeSum_eq_emeraldMass
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    emeraldWeilWindowPrimeSum K n = (emeraldMass K n : Complex) := by
  rw [emeraldWeilWindowPrimeSum_eq_mass_sum K n hn hsupp]
  simp [emeraldMass]

end
end KernelEsmeralda
