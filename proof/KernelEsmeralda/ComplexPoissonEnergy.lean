import KernelEsmeralda.ComplexPoissonTarget
import KernelEsmeralda.ImaginaryPhiDepthQuantitative
import Zeta23.Taper.Fourier

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace KernelEsmeralda

noncomputable section

/-- Conjugation commutes with a real lattice shift for the real-even taper. -/
theorem zeta23_params_phiHat_conj_shift
    (P : Zeta23.Params) (T : Real) (z : Complex) (t : Real) :
    P.phiHat T ((starRingEnd Complex) z - (t : Complex)) =
      (starRingEnd Complex) (P.phiHat T (z - (t : Complex))) := by
  have h := Zeta23.Params.phiHat_conj
    (P := P) (T := T) (z - (t : Complex))
  simpa using h

/-- The exact positive-energy form that would follow from the missing complex
Poisson extension.  Every summand is a genuine nonnegative squared modulus.
The only unproved input is `Zeta23ComplexPoissonTarget` itself. -/
theorem zeta23ComplexPoisson_energy_of_target
    (hTarget : Zeta23ComplexPoissonTarget)
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        Complex.normSq
          (P.phiHat T (z - (P.tau T k : Complex))))
      (P.L T *
        (P.Phi T
          (Complex.I * ((2 * z.im : Real) : Complex))).re) := by
  have h := hTarget P T hP hwL z ((starRingEnd Complex) z)
  have hr := Complex.reCLM.hasSum h
  convert hr using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [zeta23_params_phiHat_conj_shift P T z (P.tau T k)]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp
  · simp only [Complex.reCLM_apply]
    have hdiff :
        z - (starRingEnd Complex) z =
          Complex.I * ((2 * z.im : Real) : Complex) := by
      apply Complex.ext
      · simp [Complex.mul_re]
      · simp [Complex.mul_im]
        ring
    rw [hdiff]
    simp [Complex.mul_re]

/-- The diagonal specialization `(z,z)` of complex Poisson fixes the full
lattice sum of complex squares at the same real value `a L^2` as on the
critical line.  Combined with the positive-energy specialization above, this
will separate the real and imaginary energies of an off-line sample vector. -/
theorem zeta23ComplexPoisson_square_of_target
    (hTarget : Zeta23ComplexPoissonTarget)
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        (P.phiHat T (z - (P.tau T k : Complex))) ^ 2)
      (((P.a T * P.L T ^ 2 : Real) : Complex)) := by
  have h := hTarget P T hP hwL z z
  convert h using 1
  · funext k
    ring
  · rw [sub_self]
    change
      (P.L T : Complex) * P.Phi T ((0 : Real) : Complex) =
        ((P.a T * P.L T ^ 2 : Real) : Complex)
    rw [Zeta23.Params.Phi_ofReal]
    rw [Zeta23.Params.PhiR_zero hP hwL]
    push_cast
    ring

end
end KernelEsmeralda
