import KernelEsmeralda.CriticalLineDyadicCount
import KernelEsmeralda.ClaudeOffLineCount
import Zeta23.Statement.SeamClosed

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A finite family of off-critical-line zeros inside a dyadic ordinate window,
plus all on-line multiplicity in that window, cannot exceed the total zero
multiplicity.  This is the exact finite-set partition behind N - N0. -/
theorem dyadic_offLine_finset_mult_add_N0_le_N
    (T : Real) (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re ≠ 1 / 2 ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    (∑ rho ∈ s, Zeta23.zetaZeroConfig.mult rho) + Zeta23.N0 T (2 * T) ≤
      Zeta23.Ncount T (2 * T) := by
  classical
  let Wfin : Finset Complex := (Zeta23.zerosIn_finite T (2 * T)).toFinset
  have hOnFinite :
      (Zeta23.zerosIn T (2 * T) ∩ {rho : Complex | rho.re = 1 / 2}).Finite :=
    (Zeta23.zerosIn_finite T (2 * T)).subset Set.inter_subset_left
  let onfin : Finset Complex := hOnFinite.toFinset

  have hsSub : carrierFinsetToComplex s ⊆ Wfin := by
    intro z hz
    unfold carrierFinsetToComplex at hz
    rw [Finset.mem_map] at hz
    obtain ⟨rho, hrhos, rfl⟩ := hz
    have hrhoZero : Zeta23.IsNontrivialZero (rho : Complex) := by
      simpa [Zeta23.zetaZeroConfig_carrier] using rho.property
    have hrhoW : (rho : Complex) ∈ Zeta23.zerosIn T (2 * T) :=
      ⟨hrhoZero, (hs rho hrhos).2.1, (hs rho hrhos).2.2⟩
    simpa [Wfin] using hrhoW

  have honSub : onfin ⊆ Wfin := by
    intro z hz
    have hzOn : z ∈ Zeta23.zerosIn T (2 * T) ∩
        {rho : Complex | rho.re = 1 / 2} := by
      simpa [onfin] using hz
    simpa [Wfin] using hzOn.1

  have hdisj : Disjoint (carrierFinsetToComplex s) onfin := by
    rw [Finset.disjoint_left]
    intro z hzs hzon
    unfold carrierFinsetToComplex at hzs
    rw [Finset.mem_map] at hzs
    obtain ⟨rho, hrhos, hrho⟩ := hzs
    have hzOn : z ∈ Zeta23.zerosIn T (2 * T) ∩
        {w : Complex | w.re = 1 / 2} := by
      simpa [onfin] using hzon
    subst z
    exact (hs rho hrhos).1 hzOn.2

  have hsumUnion :
      (∑ z ∈ carrierFinsetToComplex s ∪ onfin, Zeta23.zeroMult z) ≤
        ∑ z ∈ Wfin, Zeta23.zeroMult z := by
    exact Finset.sum_le_sum_of_subset (Finset.union_subset hsSub honSub)
  rw [Finset.sum_union hdisj] at hsumUnion

  have hsSum :
      (∑ z ∈ carrierFinsetToComplex s, Zeta23.zeroMult z) =
        ∑ rho ∈ s, Zeta23.zetaZeroConfig.mult rho := by
    simpa [Zeta23.zetaZeroConfig_mult] using carrierFinsetToComplex_sum_mult s

  have hN :
      Zeta23.Ncount T (2 * T) = ∑ z ∈ Wfin, Zeta23.zeroMult z := by
    unfold Zeta23.Ncount
    rw [finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite T (2 * T))] <;>
      simp [Wfin]

  have hN0 :
      Zeta23.N0 T (2 * T) = ∑ z ∈ onfin, Zeta23.zeroMult z := by
    unfold Zeta23.N0
    rw [finsum_mem_eq_finite_toFinset_sum _ hOnFinite] <;> simp [onfin]

  rw [hsSum, ← hN0, ← hN] at hsumUnion
  exact hsumUnion

/-- Real-valued version: every finite off-line subfamily is bounded by the
exact off-line multiplicity N - N0. -/
theorem dyadic_offLine_finset_mult_real_le_offLineMultiplicityR
    (T : Real) (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re ≠ 1 / 2 ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) ≤
      emeraldOffLineMultiplicityR T (2 * T) := by
  have hnat := dyadic_offLine_finset_mult_add_N0_le_N T s hs
  have hreal :
      (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) +
          (Zeta23.N0 T (2 * T) : Real) ≤
        (Zeta23.Ncount T (2 * T) : Real) := by
    exact_mod_cast hnat
  unfold emeraldOffLineMultiplicityR
  linarith

/-- Claude's multiplicity-aware theorem now applies to every finite off-line
subfamily of a sufficiently high dyadic window. -/
theorem dyadic_offLine_finset_mult_real_le_one_third
    (ε : Real) (hε : 0 < ε) :
    ∃ T₀ : Real, ∀ T ≥ T₀,
      ∀ s : Finset Zeta23.zetaZeroConfig.carrier,
      (∀ rho ∈ s,
        (rho : Complex).re ≠ 1 / 2 ∧
        T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) →
      (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) ≤
        (1 / 3 + ε) * (Zeta23.Ncount T (2 * T) : Real) := by
  obtain ⟨T₀, hClaude⟩ := zeta23_offLine_multiplicity_le_one_third ε hε
  refine ⟨T₀, ?_⟩
  intro T hT s hs
  exact (dyadic_offLine_finset_mult_real_le_offLineMultiplicityR T s hs).trans
    (hClaude T hT)

end
end KernelEsmeralda
