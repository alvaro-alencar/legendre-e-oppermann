import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Data.Real.Basic

namespace KernelEsmeralda

noncomputable section

/-- Abstract finite-compression bookkeeping.

If a summable energy has total mass `E`, and the complementary tail outside a
finite set costs at most `R`, then the finite compression captures at least
`E - R`.  No analytic estimate enters here; all analysis is isolated in the
tail bound `htail`. -/
theorem finite_sum_ge_total_sub_tail
    {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (s : Finset ι) {E R : ℝ}
    (hE : HasSum f E)
    (htail :
      (∑' x : (↑(s : Set ι)ᶜ), f x) ≤ R) :
    E - R ≤ ∑ x ∈ s, f x := by
  have hsplit := hE.summable.sum_add_tsum_compl (s := s)
  have htotal :
      (∑ x ∈ s, f x) + (∑' x : (↑(s : Set ι)ᶜ), f x) = E := by
    calc
      (∑ x ∈ s, f x) + (∑' x : (↑(s : Set ι)ᶜ), f x)
          = ∑' x, f x := hsplit
      _ = E := hE.tsum_eq
  linarith

end
end KernelEsmeralda