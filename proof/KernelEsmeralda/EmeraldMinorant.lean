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

end
end KernelEsmeralda
