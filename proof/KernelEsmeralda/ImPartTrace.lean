import Zeta23.ZeroSide

noncomputable section

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

/-- The trace of the negative PSD component in Zeta23's off-line block is
exactly the multiplicity-weighted finite imaginary energy of the sampled
vectors.  This is the algebraic bridge needed to feed complex-Poisson depth
information into the rank/trace machinery. -/
theorem rtrace_imPart_eq_imaginary_energy
    {ι d : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (P : D.PairReps) :
    rtrace (D.imPart P) =
      ∑ z ∈ P.R,
        (2 * D.m z : ℝ) * ∑ k : d, (D.v z k).im ^ 2 := by
  unfold Zeta23.ZeroSide.ZeroBlockData.imPart rtrace
  rw [trace_sum, map_sum]
  refine sum_congr rfl fun z hz => ?_
  rw [trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct]
  have hdot :
      ∑ k : d, D.yv z k * D.yv z k =
        (((∑ k : d, (D.v z k).im ^ 2 : ℝ)) : ℂ) := by
    push_cast
    refine sum_congr rfl fun k _ => ?_
    simp [Zeta23.ZeroSide.ZeroBlockData.yv, pow_two]
  rw [hdot]
  simp [Complex.mul_re]
  ring

end KernelEsmeralda