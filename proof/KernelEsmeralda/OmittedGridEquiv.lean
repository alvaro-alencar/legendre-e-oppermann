import KernelEsmeralda.FiniteGridIndexSet

namespace KernelEsmeralda

noncomputable section

/-- Parameterization of the omitted integer grid by two copies of `ℕ`: the
negative ray and the ray starting at `d`. -/
def omittedGridRayMap
    (P : Zeta23.Params) (T : ℝ) :
    Sum ℕ ℕ → ↑((finiteGridIndexSet P T : Set ℤ)ᶜ)
  | Sum.inl j =>
      ⟨-((j : ℤ) + 1), negative_ray_not_mem_finiteGridIndexSet P T j⟩
  | Sum.inr j =>
      ⟨(P.d T : ℤ) + (j : ℤ), right_ray_not_mem_finiteGridIndexSet P T j⟩

/-- The two-ray parameterization is injective. -/
theorem omittedGridRayMap_injective
    (P : Zeta23.Params) (T : ℝ) :
    Function.Injective (omittedGridRayMap P T) := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          apply congrArg Sum.inl
          have hv := congrArg Subtype.val hab
          change -((a : ℤ) + 1) = -((b : ℤ) + 1) at hv
          omega
      | inr b =>
          exfalso
          have hv := congrArg Subtype.val hab
          change -((a : ℤ) + 1) = (P.d T : ℤ) + (b : ℤ) at hv
          have hd0 : (0 : ℤ) ≤ (P.d T : ℤ) := by omega
          have hb0 : (0 : ℤ) ≤ (b : ℤ) := by omega
          omega
  | inr a =>
      cases b with
      | inl b =>
          exfalso
          have hv := congrArg Subtype.val hab
          change (P.d T : ℤ) + (a : ℤ) = -((b : ℤ) + 1) at hv
          have hd0 : (0 : ℤ) ≤ (P.d T : ℤ) := by omega
          have ha0 : (0 : ℤ) ≤ (a : ℤ) := by omega
          omega
      | inr b =>
          apply congrArg Sum.inr
          have hv := congrArg Subtype.val hab
          change (P.d T : ℤ) + (a : ℤ) =
            (P.d T : ℤ) + (b : ℤ) at hv
          omega

/-- Every omitted grid index lies on exactly one of the two parameterized
rays. -/
theorem omittedGridRayMap_surjective
    (P : Zeta23.Params) (T : ℝ) :
    Function.Surjective (omittedGridRayMap P T) := by
  intro k
  rcases k with ⟨k, hk⟩
  have hk' := (not_mem_finiteGridIndexSet_iff P T k).1 hk
  rcases hk' with hneg | hright
  · let j : ℕ := (-k - 1).toNat
    have hnonneg : 0 ≤ -k - 1 := by omega
    have hjcast : ((j : ℕ) : ℤ) = -k - 1 := by
      dsimp [j]
      exact Int.toNat_of_nonneg hnonneg
    refine ⟨Sum.inl j, ?_⟩
    apply Subtype.ext
    change -((j : ℤ) + 1) = k
    rw [hjcast]
    ring
  · let j : ℕ := (k - (P.d T : ℤ)).toNat
    have hnonneg : 0 ≤ k - (P.d T : ℤ) := by omega
    have hjcast : ((j : ℕ) : ℤ) = k - (P.d T : ℤ) := by
      dsimp [j]
      exact Int.toNat_of_nonneg hnonneg
    refine ⟨Sum.inr j, ?_⟩
    apply Subtype.ext
    change (P.d T : ℤ) + (j : ℤ) = k
    rw [hjcast]
    ring

/-- The omitted grid is canonically equivalent to two copies of `ℕ`. -/
def omittedGridRayEquiv
    (P : Zeta23.Params) (T : ℝ) :
    Sum ℕ ℕ ≃ ↑((finiteGridIndexSet P T : Set ℤ)ᶜ) :=
  Equiv.ofBijective (omittedGridRayMap P T)
    ⟨omittedGridRayMap_injective P T, omittedGridRayMap_surjective P T⟩

@[simp] theorem omittedGridRayEquiv_inl_val
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    ((omittedGridRayEquiv P T (Sum.inl j) :
      ↑((finiteGridIndexSet P T : Set ℤ)ᶜ)) : ℤ) =
      -((j : ℤ) + 1) := rfl

@[simp] theorem omittedGridRayEquiv_inr_val
    (P : Zeta23.Params) (T : ℝ) (j : ℕ) :
    ((omittedGridRayEquiv P T (Sum.inr j) :
      ↑((finiteGridIndexSet P T : Set ℤ)ᶜ)) : ℤ) =
      (P.d T : ℤ) + (j : ℤ) := rfl

end
end KernelEsmeralda
