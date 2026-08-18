import KernelEsmeralda.ComplexPoissonFull
import Zeta23.Taper

namespace KernelEsmeralda

noncomputable section

private def sampleValue
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : ℤ) : ℂ :=
  P.phiHat T (z - (P.tau T k : ℂ))

private def poissonBilinearRHS
    (P : Zeta23.Params) (T : ℝ) (z w : ℂ) : ℂ :=
  (P.L T : ℂ) * P.Phi T (z - w)

/-- The full-lattice bilinear Poisson identity in the parameter package used
by Zeta23. -/
theorem zeta23ComplexPoisson_bilinear
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ => sampleValue P T z k * sampleValue P T w k)
      (poissonBilinearRHS P T z w) := by
  simpa [sampleValue, poissonBilinearRHS] using
    (zeta23ComplexPoissonTarget_proved P T hP hwL z w)

/-- Replacing the second argument by its conjugate turns its sampled vector
into the pointwise complex conjugate sampled vector. -/
theorem zeta23ComplexPoisson_bilinear_conj_second
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        sampleValue P T z k * starRingEnd ℂ (sampleValue P T w k))
      (poissonBilinearRHS P T z (starRingEnd ℂ w)) := by
  have h := zeta23ComplexPoisson_bilinear
    P T hP hwL z (starRingEnd ℂ w)
  convert h using 1
  funext k
  unfold sampleValue
  have harg :
      starRingEnd ℂ w - (P.tau T k : ℂ) =
        starRingEnd ℂ (w - (P.tau T k : ℂ)) := by
    simp
  rw [harg, Zeta23.Params.phiHat_conj]

/-- Real part of the ordinary bilinear identity: `Σ (x_z x_w - y_z y_w)`. -/
theorem zeta23ComplexPoisson_bilinear_re
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        (sampleValue P T z k).re * (sampleValue P T w k).re -
          (sampleValue P T z k).im * (sampleValue P T w k).im)
      (poissonBilinearRHS P T z w).re := by
  have h := Complex.reCLM.hasSum
    (zeta23ComplexPoisson_bilinear P T hP hwL z w)
  simpa [Complex.mul_re] using h

/-- Imaginary part of the ordinary bilinear identity: `Σ (x_z y_w + y_z x_w)`. -/
theorem zeta23ComplexPoisson_bilinear_im
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        (sampleValue P T z k).re * (sampleValue P T w k).im +
          (sampleValue P T z k).im * (sampleValue P T w k).re)
      (poissonBilinearRHS P T z w).im := by
  have h := Complex.imCLM.hasSum
    (zeta23ComplexPoisson_bilinear P T hP hwL z w)
  simpa [Complex.mul_im] using h

/-- Real part with conjugated second vector: `Σ (x_z x_w + y_z y_w)`. -/
theorem zeta23ComplexPoisson_bilinear_conj_re
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        (sampleValue P T z k).re * (sampleValue P T w k).re +
          (sampleValue P T z k).im * (sampleValue P T w k).im)
      (poissonBilinearRHS P T z (starRingEnd ℂ w)).re := by
  have h := Complex.reCLM.hasSum
    (zeta23ComplexPoisson_bilinear_conj_second P T hP hwL z w)
  simpa [Complex.mul_re] using h

/-- Imaginary part with conjugated second vector:
`Σ (y_z x_w - x_z y_w)`. -/
theorem zeta23ComplexPoisson_bilinear_conj_im
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        (sampleValue P T z k).im * (sampleValue P T w k).re -
          (sampleValue P T z k).re * (sampleValue P T w k).im)
      (poissonBilinearRHS P T z (starRingEnd ℂ w)).im := by
  have h := Complex.imCLM.hasSum
    (zeta23ComplexPoisson_bilinear_conj_second P T hP hwL z w)
  simpa [Complex.mul_im] using h

/-- Exact full-lattice real-real correlation. -/
theorem zeta23ComplexPoisson_real_real_correlation
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        2 * (sampleValue P T z k).re * (sampleValue P T w k).re)
      ((poissonBilinearRHS P T z w).re +
        (poissonBilinearRHS P T z (starRingEnd ℂ w)).re) := by
  have h1 := zeta23ComplexPoisson_bilinear_re P T hP hwL z w
  have h2 := zeta23ComplexPoisson_bilinear_conj_re P T hP hwL z w
  have h := h1.add h2
  convert h using 1
  · funext k
    ring
  · ring

/-- Exact full-lattice imaginary-imaginary correlation. -/
theorem zeta23ComplexPoisson_imag_imag_correlation
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        2 * (sampleValue P T z k).im * (sampleValue P T w k).im)
      ((poissonBilinearRHS P T z (starRingEnd ℂ w)).re -
        (poissonBilinearRHS P T z w).re) := by
  have h1 := zeta23ComplexPoisson_bilinear_conj_re P T hP hwL z w
  have h2 := zeta23ComplexPoisson_bilinear_re P T hP hwL z w
  have h := h1.sub h2
  convert h using 1
  · funext k
    ring
  · ring

/-- Exact full-lattice real-imaginary correlation. -/
theorem zeta23ComplexPoisson_real_imag_correlation
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        2 * (sampleValue P T z k).re * (sampleValue P T w k).im)
      ((poissonBilinearRHS P T z w).im -
        (poissonBilinearRHS P T z (starRingEnd ℂ w)).im) := by
  have h1 := zeta23ComplexPoisson_bilinear_im P T hP hwL z w
  have h2 := zeta23ComplexPoisson_bilinear_conj_im P T hP hwL z w
  have h := h1.sub h2
  convert h using 1
  · funext k
    ring
  · ring

/-- Exact full-lattice imaginary-real correlation. -/
theorem zeta23ComplexPoisson_imag_real_correlation
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z w : ℂ) :
    HasSum
      (fun k : ℤ =>
        2 * (sampleValue P T z k).im * (sampleValue P T w k).re)
      ((poissonBilinearRHS P T z w).im +
        (poissonBilinearRHS P T z (starRingEnd ℂ w)).im) := by
  have h1 := zeta23ComplexPoisson_bilinear_im P T hP hwL z w
  have h2 := zeta23ComplexPoisson_bilinear_conj_im P T hP hwL z w
  have h := h1.add h2
  convert h using 1
  · funext k
    ring
  · ring

end
end KernelEsmeralda
