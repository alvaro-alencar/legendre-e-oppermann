import KernelEsmeralda.ImaginaryCompressionRaySplit
import KernelEsmeralda.ImaginaryEnergyRaySum

namespace KernelEsmeralda

noncomputable section

/-- Explicit upper bound for the total imaginary-energy lost by the finite
Zeta23 compression at a sampling point lying `D` inside both endpoints of the
dyadic window.  The two terms correspond to the omitted negative and right
grid rays. -/
theorem imaginaryCompressionLoss_le_interior
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D) (hDh : P.hgrid T < D)
    (hzL : T + D ≤ z.re)
    (hzR : z.re ≤ 2 * T - D) :
    imaginaryCompressionLoss P T z ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T) ^ 4)⁻¹ +
          ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T) ^ 4)⁻¹ +
          ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) := by
  rw [imaginaryCompressionLoss_eq_two_rays P T hP hwL z]
  exact add_le_add
    (negative_ray_imaginary_energy_tsum_le P T D hP hwL z hD hzL)
    (right_ray_imaginary_energy_tsum_le P T D hP hwL z hDh hzR)

/-- The finite imaginary energy therefore retains the full Poisson energy up
to the same explicit two-ray loss. -/
theorem finiteImaginaryEnergy_ge_full_sub_interior_tail
    (P : Zeta23.Params) (T D : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (hD : 0 < D) (hDh : P.hgrid T < D)
    (hzL : T + D ≤ z.re)
    (hzR : z.re ≤ 2 * T - D) :
    fullImaginaryEnergy P T z -
      (2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D + P.hgrid T) ^ 4)⁻¹ +
          ((D + P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T)) +
       2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 *
        (((D - P.hgrid T) ^ 4)⁻¹ +
          ((D - P.hgrid T) ^ 3)⁻¹ / (3 * P.hgrid T))) ≤
      finiteImaginaryEnergy P T z := by
  have hloss := imaginaryCompressionLoss_le_interior
    P T D hP hwL z hD hDh hzL hzR
  unfold imaginaryCompressionLoss at hloss
  linarith

end
end KernelEsmeralda
