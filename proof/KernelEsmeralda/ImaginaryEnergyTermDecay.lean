import KernelEsmeralda.ImaginaryEnergyTermNorm
import KernelEsmeralda.ComplexPoissonDecay

namespace KernelEsmeralda

noncomputable section

/-- The horizontal-decay envelope inherited from the complex taper estimate. -/
def imaginaryEnergyDecayEnvelope
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  Real.exp (|z.im| * (P.L T / 2)) * (P.L T + P.C1 T)

/-- The complex taper estimate specialized to the Zeta23 parameter package. -/
theorem zeta23_params_phiHat_complex_decay
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (s : ℝ) :
    ‖P.phiHat T (z - (s : ℂ))‖ * (1 + (z.re - s) ^ 2) ≤
      imaginaryEnergyDecayEnvelope P T z := by
  have h := zeta23_taper_phiHat_complex_decay
    hP.taper (Zeta23.Params.w_pos hP)
    (Zeta23.Params.two_w_le hwL hP) z s
  change
    ‖P.phiHat T (z - (s : ℂ))‖ * (1 + (z.re - s) ^ 2) ≤
      imaginaryEnergyDecayEnvelope P T z
  simpa [imaginaryEnergyDecayEnvelope, Zeta23.Params.C1,
    Zeta23.Params.phiHat_eq] using h

/-- After squaring the quadratic Fourier decay, one imaginary-energy summand
has a quartically weighted uniform bound.  This division-free form is chosen
so it can be summed against the `GridTailInfinite` fourth-power estimate. -/
theorem imaginaryEnergyTerm_mul_horizontal_weight_sq_le
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) (k : ℤ) :
    imaginaryEnergyTerm P T z k *
        (1 + (z.re - P.tau T k) ^ 2) ^ 2 ≤
      2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 := by
  let A : ℝ := ‖P.phiHat T (z - (P.tau T k : ℂ))‖
  let B : ℝ := 1 + (z.re - P.tau T k) ^ 2
  let C : ℝ := imaginaryEnergyDecayEnvelope P T z
  have hterm := imaginaryEnergyTerm_le_two_norm_sq P T z k
  change imaginaryEnergyTerm P T z k ≤ 2 * A ^ 2 at hterm
  have hdec := zeta23_params_phiHat_complex_decay P T hP hwL z (P.tau T k)
  change A * B ≤ C at hdec
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hC : 0 ≤ C := hAB.trans hdec
  have hsq : (A * B) ^ 2 ≤ C ^ 2 := by
    have hdiff : 0 ≤ C - A * B := sub_nonneg.mpr hdec
    have hsum : 0 ≤ C + A * B := add_nonneg hC hAB
    nlinarith [mul_nonneg hdiff hsum]
  have hmul := mul_le_mul_of_nonneg_right hterm (sq_nonneg B)
  change
    imaginaryEnergyTerm P T z k * B ^ 2 ≤
      (2 * A ^ 2) * B ^ 2 at hmul
  calc
    imaginaryEnergyTerm P T z k *
        (1 + (z.re - P.tau T k) ^ 2) ^ 2
        = imaginaryEnergyTerm P T z k * B ^ 2 := by rfl
    _ ≤ (2 * A ^ 2) * B ^ 2 := hmul
    _ = 2 * (A * B) ^ 2 := by ring
    _ ≤ 2 * C ^ 2 := by nlinarith
    _ = 2 * (imaginaryEnergyDecayEnvelope P T z) ^ 2 := by rfl

end
end KernelEsmeralda
