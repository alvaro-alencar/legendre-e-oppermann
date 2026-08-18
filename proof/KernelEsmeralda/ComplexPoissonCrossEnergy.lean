import KernelEsmeralda.ComplexPoissonConcreteEnergy

namespace KernelEsmeralda

noncomputable section

/-- The imaginary part of a complex square is twice the real-imaginary cross
term. -/
theorem complex_sq_im_eq_two_re_mul_im (z : Complex) :
    (z ^ 2).im = 2 * z.re * z.im := by
  simp [pow_two, Complex.mul_im]
  ring

/-- Exact full-lattice orthogonality of the real and imaginary sampled taper
vectors.  It is the imaginary part of the complex Poisson square identity
`Σ phiHat(z-tau_k)^2 = a L^2`, whose right-hand side is real. -/
theorem zeta23ComplexPoisson_cross_energy
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        2 *
          (P.phiHat T (z - (P.tau T k : Complex))).re *
          (P.phiHat T (z - (P.tau T k : Complex))).im)
      0 := by
  have hS := zeta23ComplexPoisson_square P T hP hwL z
  have hSim := Complex.imCLM.hasSum hS
  simpa only [Complex.imCLM_apply, Complex.ofReal_im,
    complex_sq_im_eq_two_re_mul_im] using hSim

end
end KernelEsmeralda
