import Zeta23.Defs.Counting
import KernelEsmeralda.CriticalLineDyadicBlock

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The coercion from an actual zeta zero to its underlying complex number,
packaged as a Finset embedding. -/
def zetaCarrierEmbedding : Zeta23.zetaZeroConfig.carrier ↪ Complex where
  toFun := fun rho => (rho : Complex)
  inj' := by
    intro a b h
    exact Subtype.ext h

/-- Forget the carrier subtype while preserving a finite collection of actual zeta zeros. -/
def carrierFinsetToComplex
    (s : Finset Zeta23.zetaZeroConfig.carrier) : Finset Complex :=
  s.map zetaCarrierEmbedding

theorem carrierFinsetToComplex_sum_mult
    (s : Finset Zeta23.zetaZeroConfig.carrier) :
    (∑ rho ∈ carrierFinsetToComplex s, Zeta23.zetaZeroConfig.mult rho) =
      ∑ rho ∈ s, Zeta23.zetaZeroConfig.mult rho := by
  classical
  unfold carrierFinsetToComplex
  rw [Finset.sum_map]
  rfl

/-- Any finite collection of actual zeros in the dyadic window has total
multiplicity at most the concrete Riemann-zeta count N(T,2T). -/
theorem dyadic_finset_mult_le_N
    (T : Real) (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    (∑ rho ∈ s, Zeta23.zetaZeroConfig.mult rho) ≤
      Zeta23.zetaZeroConfig.N T (2 * T) := by
  let wfin : Finset Complex :=
    (Zeta23.zetaZeroConfig.window_finite T (2 * T)).toFinset
  have hsub : carrierFinsetToComplex s ⊆ wfin := by
    intro rho hrho
    unfold carrierFinsetToComplex at hrho
    rw [Finset.mem_map] at hrho
    obtain ⟨r, hrs, hr⟩ := hrho
    subst rho
    unfold wfin
    rw [Set.Finite.mem_toFinset]
    exact ⟨r.property, (hs r hrs).1, (hs r hrs).2⟩
  have hsum :
      (∑ rho ∈ carrierFinsetToComplex s, Zeta23.zetaZeroConfig.mult rho) ≤
        ∑ rho ∈ wfin, Zeta23.zetaZeroConfig.mult rho := by
    exact Finset.sum_le_sum_of_subset hsub
  rw [carrierFinsetToComplex_sum_mult] at hsum
  have hN :
      Zeta23.zetaZeroConfig.N T (2 * T) =
        ∑ rho ∈ wfin, Zeta23.zetaZeroConfig.mult rho := by
    unfold Zeta23.ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _
      (Zeta23.zetaZeroConfig.window_finite T (2 * T))]
  simpa [hN] using hsum

theorem dyadic_finset_mult_real_le_N
    (T : Real) (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    (∑ rho ∈ s, (Zeta23.zetaZeroConfig.mult rho : Real)) ≤
      (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := by
  exact_mod_cast dyadic_finset_mult_le_N T s hs

/-- Dyadic critical-line block estimate in terms of the actual zeta counting function. -/
theorem emeraldCriticalDyadicBlock_bound_by_N
    (n : Nat) (hn : 1 ≤ n) (T : Real) (hT : 0 < T)
    (s : Finset Zeta23.zetaZeroConfig.carrier)
    (hs : ∀ rho ∈ s,
      (rho : Complex).re = 1 / 2 ∧
      T < (rho : Complex).im ∧ (rho : Complex).im ≤ 2 * T) :
    ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
      ((16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2) *
        (Zeta23.zetaZeroConfig.N T (2 * T) : Real) := by
  have hblock := emeraldCriticalDyadicBlock_bound_by_multiplicity n hn T hT s hs
  have hcount := dyadic_finset_mult_real_le_N T s (fun rho hrho => (hs rho hrho).2)
  have hC :
      0 ≤ (16 * Zeta23.Taper.l1Deriv2 Zeta23.Taper.smoothstep * (n : Real) ^ 2) / T ^ 2 := by
    exact div_nonneg (smoothstep_decay_constant_nonneg n) (sq_nonneg T)
  exact hblock.trans (mul_le_mul_of_nonneg_left hcount hC)

end
end KernelEsmeralda
