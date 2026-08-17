import KernelEsmeralda.OmittedGridEquiv
import KernelEsmeralda.ComplexPoissonImaginaryEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace KernelEsmeralda

noncomputable section

/-- Any summable series on the integer grid splits over the omitted indices
into the negative ray and the ray beginning at `d`. -/
theorem tsum_omittedGrid_eq_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (f : ℤ → ℝ) (hf : Summable f) :
    (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ), f k) =
      (∑' j : ℕ, f (-((j : ℤ) + 1))) +
      (∑' j : ℕ, f ((P.d T : ℤ) + (j : ℤ))) := by
  let S : Set ℤ := (finiteGridIndexSet P T : Set ℤ)ᶜ
  let e : Sum ℕ ℕ ≃ S := omittedGridRayEquiv P T
  let g : Sum ℕ ℕ → ℝ := fun q => f (e q)
  have hcomp : Summable (fun k : S => f k) := hf.subtype S
  have hg : Summable g := by
    exact (e.summable_iff).2 hcomp
  have hreindex :
      (∑' k : S, f k) = ∑' q : Sum ℕ ℕ, g q := by
    have hs' : HasSum g (∑' k : S, f k) := by
      exact (e.hasSum_iff).2 hcomp.hasSum
    exact hs'.tsum_eq.symm
  change (∑' k : S, f k) = _
  rw [hreindex, hg.tsum_sum]
  congr 1
  · apply tsum_congr
    intro j
    change f (e (Sum.inl j)) = f (-((j : ℤ) + 1))
    congr 1
    exact omittedGridRayEquiv_inl_val P T j
  · apply tsum_congr
    intro j
    change f (e (Sum.inr j)) = f ((P.d T : ℤ) + (j : ℤ))
    congr 1
    exact omittedGridRayEquiv_inr_val P T j

/-- The imaginary-energy series over the full integer grid is summable by the
complex Poisson identity. -/
theorem imaginaryEnergyTerm_summable
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    Summable (imaginaryEnergyTerm P T z) := by
  have hpoisson := zeta23ComplexPoisson_imaginary_energy P T hP hwL z
  have hallHas :
      HasSum (imaginaryEnergyTerm P T z) (fullImaginaryEnergy P T z) := by
    unfold imaginaryEnergyTerm fullImaginaryEnergy
    simpa using hpoisson
  exact hallHas.summable

/-- The exact omitted-grid imaginary-energy tail is the sum of the two natural
number rays. -/
theorem imaginaryEnergyTail_eq_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
        imaginaryEnergyTerm P T z k) =
      (∑' j : ℕ, imaginaryEnergyTerm P T z (-((j : ℤ) + 1))) +
      (∑' j : ℕ,
        imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ))) :=
  tsum_omittedGrid_eq_two_rays P T (imaginaryEnergyTerm P T z)
    (imaginaryEnergyTerm_summable P T hP hwL z)

/-- Consequently the abstract compression loss itself is exactly the sum of
the two omitted imaginary-energy rays. -/
theorem imaginaryCompressionLoss_eq_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    imaginaryCompressionLoss P T z =
      (∑' j : ℕ, imaginaryEnergyTerm P T z (-((j : ℤ) + 1))) +
      (∑' j : ℕ,
        imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ))) := by
  rw [imaginaryCompressionLoss_eq_tail P T hP hwL z]
  exact imaginaryEnergyTail_eq_two_rays P T hP hwL z

end
end KernelEsmeralda
