import KernelEsmeralda.ComplexPoissonImaginaryEnergy
import Zeta23.ZeroSide

namespace KernelEsmeralda

noncomputable section

/-- Full-lattice imaginary energy attached to a complex spectral point. -/
def fullImaginaryEnergy (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  P.L T *
      (P.Phi T
        (Complex.I * ((2 * z.im : ℝ) : ℂ))).re -
    P.a T * P.L T ^ 2

/-- Imaginary energy retained by the finite compression `0 ≤ k < d` used in
Zeta23's zero-side matrices. -/
def finiteImaginaryEnergy (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ k : Fin (P.d T),
    2 * (P.phiHat T (z - (P.tau T (k : ℤ) : ℂ))).im ^ 2

/-- Energy lost when passing from the full integer lattice to the finite
Zeta23 compression. -/
def imaginaryCompressionLoss (P : Zeta23.Params) (T : ℝ) (z : ℂ) : ℝ :=
  fullImaginaryEnergy P T z - finiteImaginaryEnergy P T z

/-- The finite compression cannot contain more imaginary energy than the full
Poisson lattice.  Hence the compression loss is always nonnegative. -/
theorem imaginaryCompressionLoss_nonneg
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    0 ≤ imaginaryCompressionLoss P T z := by
  have hsum := zeta23ComplexPoisson_imaginary_energy P T hP hwL z
  let e : Fin (P.d T) ↪ ℤ :=
    ⟨fun k => ((k : ℕ) : ℤ), fun a b h => by
      apply Fin.ext
      exact Int.ofNat.inj h⟩
  have hfin :
      finiteImaginaryEnergy P T z ≤ fullImaginaryEnergy P T z := by
    unfold finiteImaginaryEnergy fullImaginaryEnergy
    have hle := sum_le_hasSum (Finset.univ.map e)
      (fun i _ => by positivity) hsum
    rw [Finset.sum_map] at hle
    simpa [e] using hle
  unfold imaginaryCompressionLoss
  linarith

/-- Any quantitative upper bound for the compression loss converts the exact
full-lattice Poisson energy into a lower bound for the finite matrix energy. -/
theorem finiteImaginaryEnergy_ge_full_sub_lossBound
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) {R : ℝ}
    (hloss : imaginaryCompressionLoss P T z ≤ R) :
    fullImaginaryEnergy P T z - R ≤ finiteImaginaryEnergy P T z := by
  unfold imaginaryCompressionLoss at hloss
  linarith

end
end KernelEsmeralda