import Zeta23.Taper.Norms
import KernelEsmeralda.LinearCore

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

end
end KernelEsmeralda
