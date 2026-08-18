import KernelEsmeralda.ComplexSquareTailDecay
import KernelEsmeralda.OmittedGridEquiv
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace KernelEsmeralda

noncomputable section

/-- One complex term of the square Poisson series. -/
def complexSquareTerm
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : ℤ) : ℂ :=
  (P.phiHat T (z - (P.tau T k : ℂ))) ^ 2

/-- The finite complex square sum is exactly the sum over retained integer
indices. -/
theorem finiteComplexSquareSum_eq_grid_sum
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    finiteComplexSquareSum P T z =
      ∑ k ∈ finiteGridIndexSet P T, complexSquareTerm P T z k := by
  unfold finiteComplexSquareSum finiteGridIndexSet complexSquareTerm
  rw [Finset.sum_map]
  rfl

/-- The full complex-square series is summable by the exact Poisson square
identity. -/
theorem complexSquareTerm_summable
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    Summable (complexSquareTerm P T z) := by
  have h := zeta23ComplexPoisson_square P T hP hwL z
  simpa [complexSquareTerm] using h.summable

/-- Any summable complex series on the omitted integer grid splits into the
negative and right rays. -/
set_option maxHeartbeats 600000 in
theorem tsum_omittedGrid_eq_two_rays_complex
    (P : Zeta23.Params) (T : ℝ)
    (f : ℤ → ℂ) (hf : Summable f) :
    (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ), f k) =
      (∑' j : ℕ, f (-((j : ℤ) + 1))) +
      (∑' j : ℕ, f ((P.d T : ℤ) + (j : ℤ))) := by
  let S : Set ℤ := (finiteGridIndexSet P T : Set ℤ)ᶜ
  let e : Sum ℕ ℕ ≃ S := omittedGridRayEquiv P T
  let g : Sum ℕ ℕ → ℂ := fun q => f (e q)
  have hcomp : Summable (fun k : S => f k) := hf.subtype S
  have hs' : HasSum g (∑' k : S, f k) := by
    exact (e.hasSum_iff).2 hcomp.hasSum
  have hg : Summable g := hs'.summable
  have hreindex :
      (∑' k : S, f k) = ∑' q : Sum ℕ ℕ, g q :=
    hs'.tsum_eq.symm
  have hleft : Summable (g ∘ Sum.inl) :=
    hg.comp_injective Sum.inl_injective
  have hright : Summable (g ∘ Sum.inr) :=
    hg.comp_injective Sum.inr_injective
  change (∑' k : S, f k) = _
  rw [hreindex, hleft.tsum_sum hright]
  congr 1

/-- Exact finite-plus-tail decomposition of the complex square identity. -/
theorem finiteComplexSquareSum_add_tail_eq_baseline
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    finiteComplexSquareSum P T z +
        (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
          complexSquareTerm P T z k) =
      ((P.a T * P.L T ^ 2 : ℝ) : ℂ) := by
  have hsum := zeta23ComplexPoisson_square P T hP hwL z
  have hsumm := complexSquareTerm_summable P T hP hwL z
  let s : Finset ℤ := finiteGridIndexSet P T
  have hsplit := hsumm.sum_add_tsum_compl (s := s)
  calc
    finiteComplexSquareSum P T z +
        (∑' k : ↑((finiteGridIndexSet P T : Set ℤ)ᶜ),
          complexSquareTerm P T z k)
        = (∑ k ∈ s, complexSquareTerm P T z k) +
            (∑' k : ↑((s : Set ℤ)ᶜ), complexSquareTerm P T z k) := by
              rw [finiteComplexSquareSum_eq_grid_sum]
              rfl
    _ = ∑' k : ℤ, complexSquareTerm P T z k := hsplit
    _ = ((P.a T * P.L T ^ 2 : ℝ) : ℂ) := by
      simpa [complexSquareTerm] using hsum.tsum_eq

/-- The finite square error is exactly the negative of the two omitted rays. -/
theorem finiteComplexSquare_error_eq_neg_two_rays
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    finiteComplexSquareSum P T z -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ) =
      -((∑' j : ℕ, complexSquareTerm P T z (-((j : ℤ) + 1))) +
        (∑' j : ℕ,
          complexSquareTerm P T z ((P.d T : ℤ) + (j : ℤ)))) := by
  have hfull := finiteComplexSquareSum_add_tail_eq_baseline
    P T hP hwL z
  have hsplit := tsum_omittedGrid_eq_two_rays_complex
    P T (complexSquareTerm P T z)
      (complexSquareTerm_summable P T hP hwL z)
  rw [hsplit] at hfull
  rw [← hfull]
  ring

/-- Explicit interior bound for the norm of the finite complex-square error.
The coefficient is one, compared with coefficient two in the imaginary-energy
loss. -/
theorem finiteComplexSquare_error_norm_le_interior
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D) (hDh : P.hgrid T < D)
    (hzL : T + D ≤ z.re)
    (hzR : z.re ≤ 2 * T - D) :
    ‖finiteComplexSquareSum P T z -
        ((P.a T * P.L T ^ 2 : ℝ) : ℂ)‖ ≤
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T) ^ 4)⁻¹ +
          ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
      (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T) ^ 4)⁻¹ +
          ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  rw [finiteComplexSquare_error_eq_neg_two_rays P T hP hwL z, norm_neg]
  let fL : ℕ → ℂ := fun j => complexSquareTerm P T z (-((j : ℤ) + 1))
  let fR : ℕ → ℂ := fun j =>
    complexSquareTerm P T z ((P.d T : ℤ) + (j : ℤ))
  have hnormL : Summable (fun j : ℕ => ‖fL j‖) := by
    simpa [fL, complexSquareTerm, complexSquareNormTerm] using
      summable_negative_ray_complexSquareNormTerm
        P T D hP hwL z hD hzL
  have hnormR : Summable (fun j : ℕ => ‖fR j‖) := by
    simpa [fR, complexSquareTerm, complexSquareNormTerm] using
      summable_right_ray_complexSquareNormTerm
        P T D hP hwL z hDh hzR
  have htri := norm_add_le (∑' j, fL j) (∑' j, fR j)
  have hLnorm := norm_tsum_le_tsum_norm hnormL
  have hRnorm := norm_tsum_le_tsum_norm hnormR
  have hLtail := negative_ray_complexSquareNorm_tsum_le
    P T D hP hwL z hD hzL
  have hRtail := right_ray_complexSquareNorm_tsum_le
    P T D hP hwL z hDh hzR
  change ‖(∑' j, fL j) + (∑' j, fR j)‖ ≤ _
  calc
    ‖(∑' j, fL j) + (∑' j, fR j)‖
        ≤ ‖∑' j, fL j‖ + ‖∑' j, fR j‖ := htri
    _ ≤ (∑' j, ‖fL j‖) + (∑' j, ‖fR j‖) :=
      add_le_add hLnorm hRnorm
    _ ≤ (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D + P.hgrid T) ^ 4)⁻¹ +
            ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
        (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
          (((D - P.hgrid T) ^ 4)⁻¹ +
            ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
      exact add_le_add (by simpa [fL, complexSquareTerm, complexSquareNormTerm] using hLtail)
        (by simpa [fR, complexSquareTerm, complexSquareNormTerm] using hRtail)

end
end KernelEsmeralda
