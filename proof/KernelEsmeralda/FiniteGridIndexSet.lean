import KernelEsmeralda.ImaginaryCompressionTail

namespace KernelEsmeralda

noncomputable section

/-- The integer image of the finite compression is exactly the interval
`0 ≤ k < d`. -/
theorem mem_finiteGridIndexSet_iff
    (P : Zeta23.Params) (T : ℝ) (k : ℤ) :
    k ∈ finiteGridIndexSet P T ↔
      0 ≤ k ∧ k < (P.d T : ℤ) := by
  constructor
  · intro hk
    rcases Finset.mem_map.mp hk with ⟨a, ha, rfl⟩
    change 0 ≤ (((a : Fin (P.d T)) : ℕ) : ℤ) ∧
      (((a : Fin (P.d T)) : ℕ) : ℤ) < (P.d T : ℤ)
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast a.isLt
  · rintro ⟨hk0, hkd⟩
    have hkcast : ((k.toNat : ℕ) : ℤ) = k :=
      Int.toNat_of_nonneg hk0
    have hnatInt : ((k.toNat : ℕ) : ℤ) < (P.d T : ℤ) := by
      simpa [hkcast] using hkd
    have hnat : k.toNat < P.d T := by
      exact_mod_cast hnatInt
    let a : Fin (P.d T) := ⟨k.toNat, hnat⟩
    apply Finset.mem_map.mpr
    refine ⟨a, Finset.mem_univ a, ?_⟩
    change ((k.toNat : ℕ) : ℤ) = k
    exact hkcast

/-- An integer index is omitted precisely when it lies on one of the two
infinite rays: negative, or at least `d`. -/
theorem not_mem_finiteGridIndexSet_iff
    (P : Zeta23.Params) (T : ℝ) (k : ℤ) :
    k ∉ finiteGridIndexSet P T ↔
      k < 0 ∨ (P.d T : ℤ) ≤ k := by
  rw [not_congr (mem_finiteGridIndexSet_iff P T k)]
  omega

/-- Every point of the negative parameterized ray is omitted. -/
theorem negative_ray_not_mem_finiteGridIndexSet
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    -((j : ℤ) + 1) ∉ finiteGridIndexSet P T := by
  rw [not_mem_finiteGridIndexSet_iff]
  left
  omega

/-- Every point of the right parameterized ray is omitted. -/
theorem right_ray_not_mem_finiteGridIndexSet
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    (P.d T : ℤ) + (j : ℤ) ∉ finiteGridIndexSet P T := by
  rw [not_mem_finiteGridIndexSet_iff]
  right
  omega

end
end KernelEsmeralda
