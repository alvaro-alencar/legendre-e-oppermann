import KernelEsmeralda.LogBarrierCriterion
import KernelEsmeralda.EmeraldMinorant

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Subtracting a nonnegative correction from an admissible upper minorant
preserves the only pointwise condition used by the final Legendre detector:
`K ≤ 1`.  No lower bound on the corrected kernel is required here. -/
theorem sub_nonneg_correction_le_one
    (K H : Real → Real)
    (hK : ∀ u : Real, K u ≤ 1)
    (hH : ∀ u : Real, 0 ≤ H u) :
    ∀ u : Real, K u - H u ≤ 1 := by
  intro u
  linarith [hK u, hH u]

/-- Support is also preserved when both the baseline and correction are
supported in the same Legendre logarithmic window. -/
theorem support_sub_subset_legendre_window
    (K H : Real → Real) (n : Nat)
    (hK : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hH : Function.support H ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    Function.support (fun u => K u - H u) ⊆
      Ioo (emeraldLogLeft n) (emeraldLogRight n) := by
  intro u hu
  by_contra hout
  have hK0 : K u = 0 := by
    by_contra hne
    exact hout (hK (Function.mem_support.mpr hne))
  have hH0 : H u = 0 := by
    by_contra hne
    exact hout (hH (Function.mem_support.mpr hne))
  exact hu (by simp [hK0, hH0])

/-- The von-Mangoldt mass is exactly linear under a signed correction. -/
theorem emeraldMass_sub
    (K H : Real → Real) (n : Nat) :
    emeraldMass (fun u => K u - H u) n =
      emeraldMass K n - emeraldMass H n := by
  unfold emeraldMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Exact detector for a signed correction.  A correction may be negative in
the final kernel; it is enough that the baseline is bounded above by one,
the subtracted correction is nonnegative, and the corrected mass still beats
the prime-power barrier. -/
theorem legendre_of_signed_correction_mass
    (K H : Real → Real)
    (hK : ∀ u : Real, K u ≤ 1)
    (hH : ∀ u : Real, 0 ≤ H u)
    (n : Nat) (hn : 2 ≤ n)
    (hmass : primePowerLogBarrier n < emeraldMass K n - emeraldMass H n) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply legendre_of_emeraldMass_gt_logBarrier
    (fun u => K u - H u)
    (sub_nonneg_correction_le_one K H hK hH) n hn
  rw [emeraldMass_sub]
  exact hmass

/-- Budget form: if the correction costs at most `B` units of von-Mangoldt
mass, it suffices for the baseline mass to beat `primePowerLogBarrier + B`. -/
theorem legendre_of_signed_correction_budget
    (K H : Real → Real)
    (hK : ∀ u : Real, K u ≤ 1)
    (hH : ∀ u : Real, 0 ≤ H u)
    (n : Nat) (hn : 2 ≤ n)
    (B : Real)
    (hcost : emeraldMass H n ≤ B)
    (hbase : primePowerLogBarrier n + B < emeraldMass K n) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply legendre_of_signed_correction_mass K H hK hH n hn
  linarith

end
end KernelEsmeralda
