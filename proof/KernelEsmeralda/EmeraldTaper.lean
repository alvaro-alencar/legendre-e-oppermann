import Zeta23.Taper.Norms
import KernelEsmeralda.LinearCore

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

def emeraldTaperCenter (n : Nat) : Real :=
  (emeraldLogLeft n + emeraldLogRight n) / 2

def emeraldTaperLength (n : Nat) : Real :=
  emeraldLogRight n - emeraldLogLeft n

def emeraldTaperWidth (n : Nat) : Real :=
  min (emeraldLinearCoreLeft n - emeraldLogLeft n)
      (emeraldLogRight n - emeraldLinearCoreRight n)

def emeraldTaperWeight (n : Nat) (u : Real) : Real :=
  Zeta23.Taper.phi Zeta23.Taper.smoothstep
    (emeraldTaperLength n) (emeraldTaperWidth n)
    (u - emeraldTaperCenter n)

theorem emeraldTaperWidth_pos (n : Nat) (hn : 1 ≤ n) :
    0 < emeraldTaperWidth n := by
  have h := emeraldLinearCore_chain n hn
  unfold emeraldTaperWidth
  exact lt_min (sub_pos.mpr h.1) (sub_pos.mpr h.2.2)

theorem two_mul_emeraldTaperWidth_le_length (n : Nat) (hn : 1 ≤ n) :
    2 * emeraldTaperWidth n ≤ emeraldTaperLength n := by
  have h := emeraldLinearCore_chain n hn
  have hwL : emeraldTaperWidth n ≤ emeraldLinearCoreLeft n - emeraldLogLeft n := by
    unfold emeraldTaperWidth
    exact min_le_left _ _
  have hwR : emeraldTaperWidth n ≤ emeraldLogRight n - emeraldLinearCoreRight n := by
    unfold emeraldTaperWidth
    exact min_le_right _ _
  unfold emeraldTaperLength
  linarith

theorem emeraldTaper_center_sub_half_length (n : Nat) :
    emeraldTaperCenter n - emeraldTaperLength n / 2 = emeraldLogLeft n := by
  unfold emeraldTaperCenter emeraldTaperLength
  ring

theorem emeraldTaper_center_add_half_length (n : Nat) :
    emeraldTaperCenter n + emeraldTaperLength n / 2 = emeraldLogRight n := by
  unfold emeraldTaperCenter emeraldTaperLength
  ring

theorem emeraldTaperWeight_nonneg (n : Nat) (u : Real) :
    0 ≤ emeraldTaperWeight n u := by
  unfold emeraldTaperWeight
  exact Zeta23.Taper.phi_nonneg Zeta23.Taper.taperProfile_smoothstep _

theorem emeraldTaperWeight_le_one (n : Nat) (u : Real) :
    emeraldTaperWeight n u ≤ 1 := by
  unfold emeraldTaperWeight
  exact Zeta23.Taper.phi_le_one Zeta23.Taper.taperProfile_smoothstep _

theorem emeraldTaperWeight_contDiff_three (n : Nat) (hn : 1 ≤ n) :
    ContDiff Real 3 (emeraldTaperWeight n) := by
  unfold emeraldTaperWeight
  have hphi := Zeta23.Taper.phi_contDiff
    Zeta23.Taper.taperProfile_smoothstep
    (emeraldTaperWidth_pos n hn)
    (two_mul_emeraldTaperWidth_le_length n hn)
  exact hphi.comp (by fun_prop)

theorem emeraldTaperWeight_eq_one_on_linear_core
    (n : Nat) (hn : 1 ≤ n) {u : Real}
    (hu : u ∈ Icc (emeraldLinearCoreLeft n) (emeraldLinearCoreRight n)) :
    emeraldTaperWeight n u = 1 := by
  unfold emeraldTaperWeight
  apply Zeta23.Taper.phi_eq_one Zeta23.Taper.taperProfile_smoothstep
    (emeraldTaperWidth_pos n hn)
  have hwL : emeraldTaperWidth n ≤ emeraldLinearCoreLeft n - emeraldLogLeft n := by
    unfold emeraldTaperWidth
    exact min_le_left _ _
  have hwR : emeraldTaperWidth n ≤ emeraldLogRight n - emeraldLinearCoreRight n := by
    unfold emeraldTaperWidth
    exact min_le_right _ _
  rw [abs_le]
  constructor
  · rw [emeraldTaper_center_sub_half_length] at *
    unfold emeraldTaperLength emeraldTaperCenter
    linarith [hu.1]
  · rw [emeraldTaper_center_add_half_length] at *
    unfold emeraldTaperLength emeraldTaperCenter
    linarith [hu.2]

theorem emeraldTaperWeight_support
    (n : Nat) (hn : 1 ≤ n) :
    Function.support (emeraldTaperWeight n) ⊆
      Ioo (emeraldLogLeft n) (emeraldLogRight n) := by
  intro u hu
  rw [Function.mem_support] at hu
  have hw := emeraldTaperWidth_pos n hn
  constructor
  · by_contra hleft
    have hul : u ≤ emeraldLogLeft n := le_of_not_gt hleft
    apply hu
    unfold emeraldTaperWeight
    apply Zeta23.Taper.phi_eq_zero Zeta23.Taper.taperProfile_smoothstep hw
    have hc : emeraldTaperLength n / 2 = emeraldTaperCenter n - emeraldLogLeft n := by
      linarith [emeraldTaper_center_sub_half_length n]
    rw [hc]
    calc
      emeraldTaperCenter n - emeraldLogLeft n ≤ emeraldTaperCenter n - u := by linarith
      _ = -(u - emeraldTaperCenter n) := by ring
      _ ≤ |u - emeraldTaperCenter n| := neg_le_abs _
  · by_contra hright
    have hur : emeraldLogRight n ≤ u := le_of_not_gt hright
    apply hu
    unfold emeraldTaperWeight
    apply Zeta23.Taper.phi_eq_zero Zeta23.Taper.taperProfile_smoothstep hw
    have hc : emeraldTaperLength n / 2 = emeraldLogRight n - emeraldTaperCenter n := by
      linarith [emeraldTaper_center_add_half_length n]
    rw [hc]
    calc
      emeraldLogRight n - emeraldTaperCenter n ≤ u - emeraldTaperCenter n := by linarith
      _ ≤ |u - emeraldTaperCenter n| := le_abs_self _

theorem emeraldTaperWeight_hasCompactSupport
    (n : Nat) (hn : 1 ≤ n) :
    HasCompactSupport (emeraldTaperWeight n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (emeraldLogLeft n) (emeraldLogRight n)) isCompact_Icc
  exact (emeraldTaperWeight_support n hn).trans Ioo_subset_Icc_self

end
end KernelEsmeralda
