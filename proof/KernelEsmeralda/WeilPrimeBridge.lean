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

/-- Se o peso é não nulo em `log m`, então `m` pertence à janela quadrática. -/
theorem mem_square_window_of_emerald_log_ne_zero
    (K : Real → Real) (n m : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hK : K (Real.log (m : Real)) ≠ 0) :
    m ∈ Finset.Ioc (n ^ 2) ((n + 1) ^ 2) := by
  have hs : Real.log (m : Real) ∈ Function.support K := hK
  have hi := hsupp hs
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  have hnpos : (0 : Real) < n := by exact_mod_cast hnposNat
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hsquares : lowerSquare n < upperSquare n := by
    unfold lowerSquare upperSquare
    have hsucc : (n : Real) < (((n + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.lt_succ_self n
    nlinarith
  have hupos : 0 < upperSquare n := hlpos.trans hsquares
  have hleftlog : 0 < emeraldLogLeft n := by
    unfold emeraldLogLeft
    exact Real.log_pos (by
      unfold lowerSquare
      nlinarith [sq_nonneg ((n : Real) - 1)])
  have hlogpos : 0 < Real.log (m : Real) := hleftlog.trans hi.1
  have hmgt1 : (1 : Real) < m :=
    (Real.log_pos_iff (Nat.cast_nonneg m)).1 hlogpos
  have hmpos : (0 : Real) < m := zero_lt_one.trans hmgt1
  have hloR : lowerSquare n < (m : Real) :=
    (Real.log_lt_log_iff hlpos hmpos).1 hi.1
  have hupR : (m : Real) < upperSquare n :=
    (Real.log_lt_log_iff hmpos hupos).1 hi.2
  rw [Finset.mem_Ioc]
  constructor
  · unfold lowerSquare at hloR
    exact_mod_cast hloR
  · unfold upperSquare at hupR
    exact_mod_cast hupR

end
end KernelEsmeralda
