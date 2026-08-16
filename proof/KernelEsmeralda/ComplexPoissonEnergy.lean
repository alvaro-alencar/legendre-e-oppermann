import KernelEsmeralda.ComplexPoissonTarget
import KernelEsmeralda.ImaginaryPhiDepthQuantitative
import Zeta23.Taper.Fourier

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace KernelEsmeralda

noncomputable section

/-- Because the taper is real and even, its paper Fourier transform satisfies
`phiHat(conj z) = conj(phiHat z)` at every complex point. -/
theorem zeta23_taper_phiHat_conj
    {ϱ : Real → Real} {L w : Real} (z : Complex) :
    Complex.conj (Zeta23.Taper.phiHat ϱ L w z) =
      Zeta23.Taper.phiHat ϱ L w (Complex.conj z) := by
  unfold Zeta23.Taper.phiHat
  calc
    Complex.conj
        (Zeta23.paperFT (fun u => (Zeta23.Taper.phi ϱ L w u : Complex)) z)
        = Zeta23.paperFT
            (fun u => (Zeta23.Taper.phi ϱ L w u : Complex))
            (-Complex.conj z) :=
          Zeta23.Taper.conj_paperFT_ofReal
            (Zeta23.Taper.phi ϱ L w) z
    _ = Zeta23.paperFT
          (fun u => (Zeta23.Taper.phi ϱ L w u : Complex))
          (Complex.conj z) := by
          exact Zeta23.Taper.paperFT_neg_of_even
            (v := fun u => Zeta23.Taper.phi ϱ L w u)
            (fun u => Zeta23.Taper.phi_even u)
            (Complex.conj z)

/-- Conjugation commutes with a real lattice shift. -/
theorem zeta23_params_phiHat_conj_shift
    (P : Zeta23.Params) (T : Real) (z : Complex) (t : Real) :
    P.phiHat T (Complex.conj z - (t : Complex)) =
      Complex.conj (P.phiHat T (z - (t : Complex))) := by
  have h := zeta23_taper_phiHat_conj
    (ϱ := P.ϱ) (L := P.L T) (w := P.w)
    (z - (t : Complex))
  rw [map_sub, Complex.conj_ofReal] at h
  simpa [Zeta23.Params.phiHat_eq] using h.symm

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
  have h := hTarget P T hP hwL z (Complex.conj z)
  have hr := Complex.reCLM.hasSum h
  convert hr using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [zeta23_params_phiHat_conj_shift P T z (P.tau T k)]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp
  · simp only [Complex.reCLM_apply]
    have hdiff :
        z - Complex.conj z =
          Complex.I * ((2 * z.im : Real) : Complex) := by
      apply Complex.ext
      · simp [Complex.mul_re]
      · simp [Complex.mul_im]
    rw [hdiff]
    simp [Complex.mul_re]

end
end KernelEsmeralda
