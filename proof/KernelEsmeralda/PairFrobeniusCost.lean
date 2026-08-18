import KernelEsmeralda.PairTraceBalance
import Zeta23.LinAlg.RankTrace

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A PSD matrix of rank at most `r` pays a Frobenius cost for carrying trace.
This is the `Q = 0` specialization of Claude's rank-trace inequality. -/
theorem frobSq_ge_linear_trace_of_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {r : Nat} (hr : A.rank ≤ r)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace A - c ^ 2 / 4 * r ≤ frobSq A := by
  have hzero : (0 : Matrix d d ℂ).IsHermitian := by simp
  have hpos0 : posIndex hzero = 0 := by
    apply posIndex_eq_zero_of_hermForm_nonpos hzero
    intro x
    simp [hermForm]
  have hb : posIndex hzero ≤ 0 := by simp [hpos0]
  have h := rank_trace_ineq hA hzero hr hb hc
  simpa using h

/-- A lower bound for the trace can be inserted into the same Frobenius cost. -/
theorem frobSq_ge_linear_trace_lower_of_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {r : Nat} (hr : A.rank ≤ r)
    {R0 c : ℝ} (hR0 : R0 ≤ rtrace A) (hc : 0 < c) :
    c * R0 - c ^ 2 / 4 * r ≤ frobSq A := by
  have hbase := frobSq_ge_linear_trace_of_posSemidef hA hr hc
  have hmul := mul_le_mul_of_nonneg_left hR0 hc.le
  linarith

/-- Applied to the real PSD half of an off-line zero block, the number of
reflection pairs is the rank budget. -/
theorem frobSq_rePart_ge_linear_trace_lower
    {ι d : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d)
    (R : D.PairReps)
    {R0 c : ℝ}
    (hR0 : R0 ≤ rtrace (D.rePart R))
    (hc : 0 < c) :
    c * R0 - c ^ 2 / 4 * R.p ≤ frobSq (D.rePart R) := by
  exact frobSq_ge_linear_trace_lower_of_posSemidef
    (D.rePart_posSemidef R) (D.rank_rePart_le R) hR0 hc

end
end KernelEsmeralda
