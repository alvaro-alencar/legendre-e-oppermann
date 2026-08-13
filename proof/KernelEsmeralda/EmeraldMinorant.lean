import Mathlib.Geometry.Manifold.PartitionOfUnity
import KernelEsmeralda.PrimePowerWindowSqrt

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

theorem exists_smooth_emerald_minorant
    {a b c d : Real}
    (hab : a < b)
    (hcd : c < d) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc b c, K x = 1) ∧
      Function.support K ⊆ Ioo a d := by
  have hdisj : Disjoint (Iic a ∪ Ici d) (Icc b c) := by
    rw [disjoint_union_left]
    constructor
    · exact disjoint_left.2 (by
        intro x hxa hxbc
        exact (not_lt_of_ge hxa) (hab.trans_le hxbc.1))
    · exact disjoint_left.2 (by
        intro x hxd hxbc
        exact (not_lt_of_ge hxd) (hxbc.2.trans_lt hcd))
  obtain ⟨K, hKsmooth, hKrange, hKzero, hKone⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
      (modelWithCornersSelf Real Real)
      (isClosed_Iic.union isClosed_Ici) isClosed_Icc hdisj
  have hsupp : Function.support K ⊆ Ioo a d := by
    intro x hx
    have hxnot : x ∉ Iic a ∪ Ici d := by
      intro houtside
      exact hx ((hKzero x).1 houtside)
    simp only [mem_union, mem_Iic, mem_Ici, not_or, not_le] at hxnot
    exact ⟨hxnot.1, hxnot.2⟩
  refine ⟨K, hKsmooth.contDiff, ?_, ?_, ?_, hsupp⟩
  · apply HasCompactSupport.of_support_subset_isCompact
      (K := Icc a d) isCompact_Icc
    exact hsupp.trans Ioo_subset_Icc_self
  · intro x
    exact hKrange ⟨x, rfl⟩
  · intro x hx
    exact (hKone x).1 hx

/-- Extremos logarítmicos da janela entre quadrados consecutivos. -/
def emeraldLogLeft (n : Nat) : Real := Real.log (lowerSquare n)
def emeraldLogRight (n : Nat) : Real := Real.log (upperSquare n)

/-- Metade central da janela logarítmica, usada como núcleo onde o minorante vale `1`. -/
def emeraldCoreLeft (n : Nat) : Real :=
  (3 * emeraldLogLeft n + emeraldLogRight n) / 4

def emeraldCoreRight (n : Nat) : Real :=
  (emeraldLogLeft n + 3 * emeraldLogRight n) / 4

/-- Para cada `n ≥ 1` existe um Kernel de Esmeralda minorante suave,
suportado estritamente em `(log n², log (n+1)²)` e igual a `1`
na metade central dessa janela. -/
theorem exists_emerald_minorant_between_square_logs
    (n : Nat) (hn : 1 ≤ n) :
    ∃ K : Real → Real,
      ContDiff Real ∞ K ∧
      HasCompactSupport K ∧
      (∀ x : Real, 0 ≤ K x ∧ K x ≤ 1) ∧
      (∀ x ∈ Icc (emeraldCoreLeft n) (emeraldCoreRight n), K x = 1) ∧
      Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n) := by
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < n := by
    exact_mod_cast hnposNat
  have hsucc : (n : Real) < (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.lt_succ_self n
  have hlpos : 0 < lowerSquare n := by
    unfold lowerSquare
    positivity
  have hsquares : lowerSquare n < upperSquare n := by
    unfold lowerSquare upperSquare
    nlinarith
  have hlog : emeraldLogLeft n < emeraldLogRight n := by
    unfold emeraldLogLeft emeraldLogRight
    exact Real.log_lt_log hlpos hsquares
  have hleft : emeraldLogLeft n < emeraldCoreLeft n := by
    unfold emeraldCoreLeft
    linarith
  have hright : emeraldCoreRight n < emeraldLogRight n := by
    unfold emeraldCoreRight
    linarith
  exact exists_smooth_emerald_minorant hleft hright

/-- Normalização real do teste para a fórmula explícita: `k(u)=e^(u/2)K(u)`. -/
def emeraldTilt (K : Real → Real) (u : Real) : Real :=
  Real.exp (u / 2) * K u

/-- Em `u = log m`, a inclinação exponencial é exatamente `sqrt m`. -/
theorem emeraldTilt_log_eq_sqrt_mul
    (K : Real → Real) (m : Nat) (hm : 0 < m) :
    emeraldTilt K (Real.log (m : Real)) =
      Real.sqrt (m : Real) * K (Real.log (m : Real)) := by
  unfold emeraldTilt
  have hmR : (0 : Real) < m := by
    exact_mod_cast hm
  have hexp : Real.exp (Real.log (m : Real) / 2) = Real.sqrt (m : Real) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hmR]
    congr 1
    ring
  rw [hexp]

/-- O `e^(u/2)` cancela exatamente o `1/sqrt m` do lado primo de Weil. -/
theorem weil_prime_factor_normalization
    (K : Real → Real) (m : Nat) (hm : 0 < m) :
    (ArithmeticFunction.vonMangoldt m / Real.sqrt (m : Real)) *
        emeraldTilt K (Real.log (m : Real)) =
      ArithmeticFunction.vonMangoldt m * K (Real.log (m : Real)) := by
  rw [emeraldTilt_log_eq_sqrt_mul K m hm]
  have hsqrt : Real.sqrt (m : Real) ≠ 0 := by
    have hmR : (0 : Real) < m := by
      exact_mod_cast hm
    exact (Real.sqrt_pos.2 hmR).ne'
  field_simp [hsqrt]

end
end KernelEsmeralda
