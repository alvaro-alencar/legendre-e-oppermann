import KernelEsmeralda.DeepRetainedPairs

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Trace balance for the hyperbolic off-line decomposition.

Since `A = onPart + (rePart - imPart)`, a large negative/imaginary pair
energy cannot disappear: at fixed total trace it must be compensated by the
positive real pair part. -/
theorem rtrace_rePart_eq_blockA_sub_onPart_add_imPart
    {ι d : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (R : D.PairReps) :
    rtrace (D.rePart R) =
      rtrace D.blockA - rtrace D.onPart + rtrace (D.imPart R) := by
  have h := congrArg rtrace (D.blockA_decomp R)
  rw [rtrace_add, rtrace_sub] at h
  linarith

/-- The same trace balance specialized to the actual zeta block used by
Zeta23. -/
theorem rtrace_zeta_rePart_eq_Az_sub_onPart_add_imPart
    (Z : Zeta23.ZeroConfig) (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData Z T P hconj).PairReps) :
    rtrace ((Zeta23.ZeroSide.blockData Z T P hconj).rePart R) =
      rtrace (Z.Az P T) -
        rtrace (Zeta23.ZeroSide.blockData Z T P hconj).onPart +
        rtrace ((Zeta23.ZeroSide.blockData Z T P hconj).imPart R) := by
  rw [Zeta23.ZeroSide.Az_eq_blockA Z T P hconj]
  exact rtrace_rePart_eq_blockA_sub_onPart_add_imPart
    (Zeta23.ZeroSide.blockData Z T P hconj) R

/-- If the total block trace is at least `A0`, the on-line trace is at most
`On0`, and the imaginary part is at least `Im0`, then the real pair part must
carry the corresponding compensating trace. -/
theorem rtrace_rePart_lower_of_trace_budget
    {ι d : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (R : D.PairReps)
    {A0 On0 Im0 : ℝ}
    (hA : A0 ≤ rtrace D.blockA)
    (hOn : rtrace D.onPart ≤ On0)
    (hIm : Im0 ≤ rtrace (D.imPart R)) :
    A0 - On0 + Im0 ≤ rtrace (D.rePart R) := by
  rw [rtrace_rePart_eq_blockA_sub_onPart_add_imPart D R]
  linarith

end
end KernelEsmeralda
