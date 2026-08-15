import KernelEsmeralda.SignedKernelCorrection
import KernelEsmeralda.EmeraldTaper

open Set
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A perturbation fitting pointwise inside the unused headroom preserves the
only upper-bound condition required by the Legendre detector. -/
theorem add_headroom_correction_le_one
    (K C : Real → Real)
    (hC : ∀ u : Real, C u ≤ 1 - K u) :
    ∀ u : Real, K u + C u ≤ 1 := by
  intro u
  linarith [hC u]

/-- If baseline and perturbation are supported in the same Legendre window,
so is their redistribution. -/
theorem support_add_subset_legendre_window
    (K C : Real → Real) (n : Nat)
    (hK : Function.support K ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hC : Function.support C ⊆ Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    Function.support (fun u => K u + C u) ⊆
      Ioo (emeraldLogLeft n) (emeraldLogRight n) := by
  intro u hu
  by_contra hout
  have hK0 : K u = 0 := by
    by_contra hne
    exact hout (hK (Function.mem_support.mpr hne))
  have hC0 : C u = 0 := by
    by_contra hne
    exact hout (hC (Function.mem_support.mpr hne))
  exact hu (by simp [hK0, hC0])

/-- The arithmetic mass responds exactly linearly to a redistribution. -/
theorem emeraldMass_add
    (K C : Real → Real) (n : Nat) :
    emeraldMass (fun u => K u + C u) n =
      emeraldMass K n + emeraldMass C n := by
  unfold emeraldMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Detection criterion for a general headroom redistribution.  Unlike the
nonnegative-subtraction case, the correction mass may have either sign. -/
theorem legendre_of_redistributed_mass
    (K C : Real → Real)
    (hC : ∀ u : Real, C u ≤ 1 - K u)
    (n : Nat) (hn : 2 ≤ n)
    (hmass : primePowerLogBarrier n < emeraldMass K n + emeraldMass C n) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  apply legendre_of_emeraldMass_gt_logBarrier
    (fun u => K u + C u)
    (add_headroom_correction_le_one K C hC) n hn
  rw [emeraldMass_add]
  exact hmass

/-- On the linear core the explicit Emerald taper already saturates the upper
constraint `K=1`.  Therefore any admissible redistribution is necessarily
nonpositive there. -/
theorem headroom_correction_nonpos_on_emerald_linear_core
    (C : Real → Real) (n : Nat) (hn : 1 ≤ n)
    (hC : ∀ u : Real, C u ≤ 1 - emeraldTaperWeight n u)
    {u : Real}
    (hu : u ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n)) :
    C u ≤ 0 := by
  have hOne := emeraldTaperWeight_eq_one_on_linear_core n hn u hu
  have h := hC u
  rw [hOne] at h
  linarith

end
end KernelEsmeralda
