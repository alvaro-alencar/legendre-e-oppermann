import KernelEsmeralda.FiniteImaginaryEnergy

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The embedding of the finite Zeta23 compression indices into the full
integer Poisson lattice. -/
def finiteGridEmbedding (P : Zeta23.Params) (T : ℝ) : Fin (P.d T) ↪ ℤ :=
  ⟨fun k => ((k : ℕ) : ℤ), fun a b h => by
    apply Fin.ext
    exact Int.ofNat.inj h⟩

/-- Integer indices retained by the finite Zeta23 compression. -/
def finiteGridIndexSet (P : Zeta23.Params) (T : ℝ) : Finset ℤ :=
  Finset.univ.map (finiteGridEmbedding P T)

/-- One nonnegative imaginary-energy summand on the full Poisson lattice. -/
def imaginaryEnergyTerm (P : Zeta23.Params) (T : ℝ) (z : ℂ) (k : ℤ) : ℝ :=
  2 * (P.phiHat T (z - (P.tau T k : ℂ))).im ^ 2

/-- The finite matrix energy is exactly the sum over the retained integer
indices. -/
theorem finiteImaginaryEnergy_eq_grid_sum
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    finiteImaginaryEnergy P T z =
      ∑ k ∈ finiteGridIndexSet P T, imaginaryEnergyTerm P T z k := by
  unfold finiteImaginaryEnergy finiteGridIndexSet imaginaryEnergyTerm
  rw [Finset.sum_map]
  rfl

/-- The omitted imaginary-energy tail is nonnegative term by term. -/
theorem imaginaryEnergyTail_nonneg
    (P : Zeta23.Params) (T : ℝ) (z : ℂ) :
    0 ≤
      ∑' k : ((finiteGridIndexSet P T : Set ℤ)ᶜ),
        imaginaryEnergyTerm P T z k := by
  apply tsum_nonneg
  intro k
  unfold imaginaryEnergyTerm
  positivity

/-- The compression loss is not merely nonnegative: it is exactly the
nonnegative Poisson-energy tail over the omitted integer indices. -/
theorem imaginaryCompressionLoss_eq_tail
    (P : Zeta23.Params) (T : ℝ)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (z : ℂ) :
    imaginaryCompressionLoss P T z =
      ∑' k : ((finiteGridIndexSet P T : Set ℤ)ᶜ),
        imaginaryEnergyTerm P T z k := by
  have hsum := zeta23ComplexPoisson_imaginary_energy P T hP hwL z
  have hsum' :
      HasSum (imaginaryEnergyTerm P T z) (fullImaginaryEnergy P T z) := by
    unfold imaginaryEnergyTerm fullImaginaryEnergy
    simpa using hsum
  let s : Finset ℤ := finiteGridIndexSet P T
  have hsplit := hsum'.summable.sum_add_tsum_compl (s := s)
  have htotal :
      (∑ k ∈ s, imaginaryEnergyTerm P T z k) +
          (∑' k : ((s : Set ℤ)ᶜ), imaginaryEnergyTerm P T z k) =
        fullImaginaryEnergy P T z := by
    calc
      (∑ k ∈ s, imaginaryEnergyTerm P T z k) +
          (∑' k : ((s : Set ℤ)ᶜ), imaginaryEnergyTerm P T z k)
          = ∑' k, imaginaryEnergyTerm P T z k := hsplit
      _ = fullImaginaryEnergy P T z := hsum'.tsum_eq
  have hfin :
      finiteImaginaryEnergy P T z =
        ∑ k ∈ s, imaginaryEnergyTerm P T z k := by
    simpa [s] using finiteImaginaryEnergy_eq_grid_sum P T z
  unfold imaginaryCompressionLoss
  rw [hfin]
  change
    fullImaginaryEnergy P T z -
        ∑ k ∈ s, imaginaryEnergyTerm P T z k =
      ∑' k : ((s : Set ℤ)ᶜ), imaginaryEnergyTerm P T z k
  linarith

end
end KernelEsmeralda
