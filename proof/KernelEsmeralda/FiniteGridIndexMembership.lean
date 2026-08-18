import KernelEsmeralda.ImaginaryCompressionTail

namespace KernelEsmeralda

noncomputable section

/-- The integer indices retained by the finite Zeta23 compression are exactly
`0,1,...,d-1`. -/
theorem mem_finiteGridIndexSet_iff
    (P : Zeta23.Params) (T : ℝ) (k : ℤ) :
    k ∈ finiteGridIndexSet P T ↔
      0 ≤ k ∧ k < (P.d T : ℤ) := by
  constructor
  · intro hk
    unfold finiteGridIndexSet at hk
    rw [Finset.mem_map] at hk
    rcases hk with ⟨i, hi, rfl⟩
    constructor
    · exact Int.ofNat_zero_le _
    · exact_mod_cast i.2
  · rintro ⟨hk0, hkd⟩
    have hto : k.toNat < P.d T := by
      rw [Int.toNat_lt (n := P.d T) hk0]
      exact hkd
    let i : Fin (P.d T) := ⟨k.toNat, hto⟩
    unfold finiteGridIndexSet
    rw [Finset.mem_map]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    unfold finiteGridEmbedding
    exact (Int.toNat_of_nonneg hk0).symm

/-- Consequently, an omitted integer index lies on one of the two exterior
rays. -/
theorem not_mem_finiteGridIndexSet_iff
    (P : Zeta23.Params) (T : ℝ) (k : ℤ) :
    k ∉ finiteGridIndexSet P T ↔
      k < 0 ∨ (P.d T : ℤ) ≤ k := by
  rw [mem_finiteGridIndexSet_iff]
  omega

end
end KernelEsmeralda