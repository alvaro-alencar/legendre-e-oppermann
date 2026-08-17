import KernelEsmeralda.ComplexPoissonConcreteEnergy

namespace KernelEsmeralda

noncomputable section

/-- Pointwise algebra behind the imaginary-energy decomposition. -/
theorem complex_normSq_sub_sq_re_eq_two_im_sq (z : Complex) :
    Complex.normSq z - (z ^ 2).re = 2 * z.im ^ 2 := by
  simp [Complex.normSq, Complex.mul_re]
  ring

/-- Exact imaginary-energy identity furnished by the two concrete complex
Poisson formulas.  The excess of the positive norm-square energy over the
fixed complex square-sum is precisely twice the lattice energy in imaginary
parts. -/
theorem zeta23ComplexPoisson_imaginary_energy
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        2 *
          (P.phiHat T (z - (P.tau T k : Complex))).im ^ 2)
      (P.L T *
          (P.Phi T
            (Complex.I * ((2 * z.im : Real) : Complex))).re -
        P.a T * P.L T ^ 2) := by
  have hE := zeta23ComplexPoisson_energy P T hP hwL z
  have hS := zeta23ComplexPoisson_square P T hP hwL z
  have hSre := Complex.reCLM.hasSum hS
  have hSre' :
      HasSum
        (fun k : Int =>
          ((P.phiHat T (z - (P.tau T k : Complex))) ^ 2).re)
        (P.a T * P.L T ^ 2) := by
    simpa using hSre
  have hD := hE.sub hSre'
  refine hD.congr ?_
  intro k
  exact complex_normSq_sub_sq_re_eq_two_im_sq
    (P.phiHat T (z - (P.tau T k : Complex)))

end
end KernelEsmeralda
