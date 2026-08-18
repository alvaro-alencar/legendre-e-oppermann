import KernelEsmeralda.ComplexPoissonFull
import KernelEsmeralda.ComplexPoissonEnergy

namespace KernelEsmeralda

noncomputable section

/-- Concrete, hypothesis-free-in-the-project version of the positive complex
Poisson energy identity.  The only assumptions are the ordinary Zeta23
parameter-validity and window-width conditions. -/
theorem zeta23ComplexPoisson_energy
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
  exact zeta23ComplexPoisson_energy_of_target
    zeta23ComplexPoissonTarget_proved P T hP hwL z

/-- Concrete square-sum companion. -/
theorem zeta23ComplexPoisson_square
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : Complex) :
    HasSum
      (fun k : Int =>
        (P.phiHat T (z - (P.tau T k : Complex))) ^ 2)
      (((P.a T * P.L T ^ 2 : Real) : Complex)) := by
  exact zeta23ComplexPoisson_square_of_target
    zeta23ComplexPoissonTarget_proved P T hP hwL z

end
end KernelEsmeralda
