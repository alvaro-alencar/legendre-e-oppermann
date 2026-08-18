import KernelEsmeralda.ComplexBilinearCompressionError
import Zeta23.Taper

namespace KernelEsmeralda

noncomputable section

private def finiteSample
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : Fin (P.d T)) : ℂ :=
  P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))

/-- Finite bilinear sum against the pointwise conjugate second sampled vector. -/
def finiteComplexConjBilinearSum
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℂ :=
  ∑ k : Fin (P.d T),
    finiteSample P T z k * starRingEnd ℂ (finiteSample P T w k)

/-- Evaluating the second argument at `conj w` is exactly the pointwise
conjugate finite sampled vector. -/
theorem finiteComplexBilinearSum_conj_second
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteComplexBilinearSum P T z (starRingEnd ℂ w) =
      finiteComplexConjBilinearSum P T z w := by
  unfold finiteComplexBilinearSum finiteComplexConjBilinearSum
  apply Finset.sum_congr rfl
  intro k hk
  unfold complexBilinearTerm finiteSample
  have harg :
      starRingEnd ℂ w - (P.tau T (k : ℤ) : ℂ) =
        starRingEnd ℂ (w - (P.tau T (k : ℤ) : ℂ)) := by
    simp
  rw [harg, Zeta23.Params.phiHat_conj]

/-- Doubled real-real finite correlation. -/
def finiteRealRealCorrelation
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (finiteSample P T z k).re * (finiteSample P T w k).re

/-- Doubled imaginary-imaginary finite correlation. -/
def finiteImagImagCorrelation
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (finiteSample P T z k).im * (finiteSample P T w k).im

/-- Doubled real-imaginary finite correlation. -/
def finiteRealImagCorrelation
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (finiteSample P T z k).re * (finiteSample P T w k).im

/-- Doubled imaginary-real finite correlation. -/
def finiteImagRealCorrelation
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (finiteSample P T z k).im * (finiteSample P T w k).re

/-- Finite real-real correlation from the ordinary and conjugated bilinear sums. -/
theorem finiteRealRealCorrelation_eq_re_add_re_conj
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteRealRealCorrelation P T z w =
      (finiteComplexBilinearSum P T z w).re +
        (finiteComplexConjBilinearSum P T z w).re := by
  unfold finiteRealRealCorrelation finiteComplexBilinearSum
  rw [map_sum]
  unfold finiteComplexConjBilinearSum
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold complexBilinearTerm finiteSample
  simp [Complex.mul_re]
  ring

/-- Finite imaginary-imaginary correlation. -/
theorem finiteImagImagCorrelation_eq_re_conj_sub_re
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteImagImagCorrelation P T z w =
      (finiteComplexConjBilinearSum P T z w).re -
        (finiteComplexBilinearSum P T z w).re := by
  unfold finiteImagImagCorrelation finiteComplexBilinearSum
  rw [map_sum]
  unfold finiteComplexConjBilinearSum
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold complexBilinearTerm finiteSample
  simp [Complex.mul_re]
  ring

/-- Finite real-imaginary correlation. -/
theorem finiteRealImagCorrelation_eq_im_sub_im_conj
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteRealImagCorrelation P T z w =
      (finiteComplexBilinearSum P T z w).im -
        (finiteComplexConjBilinearSum P T z w).im := by
  unfold finiteRealImagCorrelation finiteComplexBilinearSum
  rw [map_sum]
  unfold finiteComplexConjBilinearSum
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold complexBilinearTerm finiteSample
  simp [Complex.mul_im]
  ring

/-- Finite imaginary-real correlation. -/
theorem finiteImagRealCorrelation_eq_im_add_im_conj
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) :
    finiteImagRealCorrelation P T z w =
      (finiteComplexBilinearSum P T z w).im +
        (finiteComplexConjBilinearSum P T z w).im := by
  unfold finiteImagRealCorrelation finiteComplexBilinearSum
  rw [map_sum]
  unfold finiteComplexConjBilinearSum
  rw [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold complexBilinearTerm finiteSample
  simp [Complex.mul_im]
  ring

/-- Real-part error is bounded by complex norm error. -/
theorem abs_re_sub_re_le_norm_sub (a b : ℂ) :
    |a.re - b.re| ≤ ‖a - b‖ := by
  have h := Complex.abs_re_le_norm (a - b)
  simpa using h

/-- Imaginary-part error is bounded by complex norm error. -/
theorem abs_im_sub_im_le_norm_sub (a b : ℂ) :
    |a.im - b.im| ≤ ‖a - b‖ := by
  have h := Complex.abs_im_le_norm (a - b)
  simpa using h

/-- Two complex approximation errors control the real-real resolved correlation. -/
theorem finiteRealRealCorrelation_error_le
    (P : Zeta23.Params) (T : ℝ) (z w K Kc : ℂ)
    {ε εc : ℝ}
    (h : ‖finiteComplexBilinearSum P T z w - K‖ ≤ ε)
    (hc : ‖finiteComplexConjBilinearSum P T z w - Kc‖ ≤ εc) :
    |finiteRealRealCorrelation P T z w - (K.re + Kc.re)| ≤ ε + εc := by
  rw [finiteRealRealCorrelation_eq_re_add_re_conj]
  have h1 := (abs_re_sub_re_le_norm_sub
    (finiteComplexBilinearSum P T z w) K).trans h
  have h2 := (abs_re_sub_re_le_norm_sub
    (finiteComplexConjBilinearSum P T z w) Kc).trans hc
  have ht := abs_add_le
    ((finiteComplexBilinearSum P T z w).re - K.re)
    ((finiteComplexConjBilinearSum P T z w).re - Kc.re)
  have := ht.trans (add_le_add h1 h2)
  convert this using 1 <;> ring

/-- Two complex approximation errors control the imaginary-imaginary correlation. -/
theorem finiteImagImagCorrelation_error_le
    (P : Zeta23.Params) (T : ℝ) (z w K Kc : ℂ)
    {ε εc : ℝ}
    (h : ‖finiteComplexBilinearSum P T z w - K‖ ≤ ε)
    (hc : ‖finiteComplexConjBilinearSum P T z w - Kc‖ ≤ εc) :
    |finiteImagImagCorrelation P T z w - (Kc.re - K.re)| ≤ ε + εc := by
  rw [finiteImagImagCorrelation_eq_re_conj_sub_re]
  have h1 := (abs_re_sub_re_le_norm_sub
    (finiteComplexBilinearSum P T z w) K).trans h
  have h2 := (abs_re_sub_re_le_norm_sub
    (finiteComplexConjBilinearSum P T z w) Kc).trans hc
  have ht := abs_sub_le
    ((finiteComplexConjBilinearSum P T z w).re - Kc.re)
    ((finiteComplexBilinearSum P T z w).re - K.re)
  have := ht.trans (add_le_add h2 h1)
  convert this using 1 <;> ring

/-- Two complex approximation errors control the real-imaginary correlation. -/
theorem finiteRealImagCorrelation_error_le
    (P : Zeta23.Params) (T : ℝ) (z w K Kc : ℂ)
    {ε εc : ℝ}
    (h : ‖finiteComplexBilinearSum P T z w - K‖ ≤ ε)
    (hc : ‖finiteComplexConjBilinearSum P T z w - Kc‖ ≤ εc) :
    |finiteRealImagCorrelation P T z w - (K.im - Kc.im)| ≤ ε + εc := by
  rw [finiteRealImagCorrelation_eq_im_sub_im_conj]
  have h1 := (abs_im_sub_im_le_norm_sub
    (finiteComplexBilinearSum P T z w) K).trans h
  have h2 := (abs_im_sub_im_le_norm_sub
    (finiteComplexConjBilinearSum P T z w) Kc).trans hc
  have ht := abs_sub_le
    ((finiteComplexBilinearSum P T z w).im - K.im)
    ((finiteComplexConjBilinearSum P T z w).im - Kc.im)
  have := ht.trans (add_le_add h1 h2)
  convert this using 1 <;> ring

/-- Two complex approximation errors control the imaginary-real correlation. -/
theorem finiteImagRealCorrelation_error_le
    (P : Zeta23.Params) (T : ℝ) (z w K Kc : ℂ)
    {ε εc : ℝ}
    (h : ‖finiteComplexBilinearSum P T z w - K‖ ≤ ε)
    (hc : ‖finiteComplexConjBilinearSum P T z w - Kc‖ ≤ εc) :
    |finiteImagRealCorrelation P T z w - (K.im + Kc.im)| ≤ ε + εc := by
  rw [finiteImagRealCorrelation_eq_im_add_im_conj]
  have h1 := (abs_im_sub_im_le_norm_sub
    (finiteComplexBilinearSum P T z w) K).trans h
  have h2 := (abs_im_sub_im_le_norm_sub
    (finiteComplexConjBilinearSum P T z w) Kc).trans hc
  have ht := abs_add_le
    ((finiteComplexBilinearSum P T z w).im - K.im)
    ((finiteComplexConjBilinearSum P T z w).im - Kc.im)
  have := ht.trans (add_le_add h1 h2)
  convert this using 1 <;> ring

end
end KernelEsmeralda
