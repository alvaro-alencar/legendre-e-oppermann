import KernelEsmeralda.OmittedGridEquiv
import KernelEsmeralda.ComplexPoissonImaginaryEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace KernelEsmeralda

noncomputable section

/-- The exact omitted-grid imaginary-energy tail is the sum of the two natural
number rays: the negative ray and the ray beginning at the first omitted
nonnegative index `d`. -/
theorem imaginaryEnergyTail_eq_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
        imaginaryEnergyTerm P T z k) =
      (∑' j : ℕ, imaginaryEnergyTerm P T z (-((j : ℤ) + 1))) +
      (∑' j : ℕ,
        imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ))) := by
  have hpoisson := zeta23ComplexPoisson_imaginary_energy P T hP hwL z
  have hallHas :
      HasSum (imaginaryEnergyTerm P T z) (fullImaginaryEnergy P T z) := by
    unfold imaginaryEnergyTerm fullImaginaryEnergy
    simpa using hpoisson
  have hall : Summable (imaginaryEnergyTerm P T z) := hallHas.summable
  let S : Set ℤ := (finiteGridIndexSet P T : Set ℤ)ᶜ
  have hcomp : Summable (fun k : S => imaginaryEnergyTerm P T z k) :=
    hall.subtype S
  let e : Sum ℕ ℕ ≃ S := omittedGridRayEquiv P T
  let g : Sum ℕ ℕ → ℝ := fun q => imaginaryEnergyTerm P T z (e q)
  have hg : Summable g := by
    exact hcomp.comp_injective e.injective
  have hsumEq :
      (∑' q : Sum ℕ ℕ, g q) =
        (∑' j : ℕ, g (Sum.inl j)) +
        (∑' j : ℕ, g (Sum.inr j)) :=
    hg.tsum_sum
  have hreindex :
      (∑' k : S, imaginaryEnergyTerm P T z k) =
        ∑' q : Sum ℕ ℕ, g q := by
    have hs : HasSum (fun k : S => imaginaryEnergyTerm P T z k)
        (∑' k : S, imaginaryEnergyTerm P T z k) := hcomp.hasSum
    have hs' : HasSum g (∑' k : S, imaginaryEnergyTerm P T z k) := by
      exact (e.hasSum_iff).2 hs
    exact hs'.tsum_eq.symm
  rw [show (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
      imaginaryEnergyTerm P T z k) =
      ∑' k : S, imaginaryEnergyTerm P T z k by rfl]
  rw [hreindex, hsumEq]
  congr 1
  · apply tsum_congr
    intro j
    change imaginaryEnergyTerm P T z (e (Sum.inl j)) =
      imaginaryEnergyTerm P T z (-((j : ℤ) + 1))
    congr 1
    exact omittedGridRayEquiv_inl_val P T j
  · apply tsum_congr
    intro j
    change imaginaryEnergyTerm P T z (e (Sum.inr j)) =
      imaginaryEnergyTerm P T z ((P.d T : ℤ) + (j : ℤ))
    congr 1
    exact omittedGridRayEquiv_inr_val P T j

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
