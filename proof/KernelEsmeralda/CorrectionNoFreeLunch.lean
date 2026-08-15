import KernelEsmeralda.SignedPoleBudget

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- A nonnegative kernel has nonnegative von-Mangoldt mass in every Legendre
window. -/
theorem emeraldMass_nonneg_of_nonneg
    (H : Real → Real) (hH : ∀ u : Real, 0 ≤ H u) (n : Nat) :
    0 ≤ emeraldMass H n := by
  unfold emeraldMass
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hH (Real.log m))

/-- Under the exact explicit balance, pole plus spectral remainder is exactly
the arithmetic mass.  Hence for a nonnegative correction it cannot be
negative. -/
theorem nonnegative_kernel_pole_add_remainder_nonneg
    (H : Real → Real) (hH : ∀ u : Real, 0 ≤ H u)
    (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support H ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance H zeroSum) :
    0 ≤ (emeraldPoleTerm H).re + emeraldSpectralRemainder H zeroSum := by
  have hmass := emeraldMass_nonneg_of_nonneg H hH n
  have hre := emeraldMass_eq_spectralBalance_re H n hn hsupp zeroSum hEF
  rw [hre] at hmass
  have hmass' :
      0 ≤ (emeraldPoleTerm H).re + (emeraldGammaTerm H).re - zeroSum.re := by
    simpa only [Complex.add_re, Complex.sub_re] using hmass
  unfold emeraldSpectralRemainder
  rw [Complex.sub_re]
  linarith

/-- No-free-lunch form.  If a nonnegative correction `H` is subtracted from a
baseline kernel, the increase `-R(H)` it can create in spectral remainder is
at most the real pole contribution that is lost. -/
theorem nonnegative_correction_spectral_gain_le_pole_cost
    (H : Real → Real) (hH : ∀ u : Real, 0 ≤ H u)
    (n : Nat) (hn : 2 ≤ n)
    (hsupp : Function.support H ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance H zeroSum) :
    -emeraldSpectralRemainder H zeroSum ≤ (emeraldPoleTerm H).re := by
  have h := nonnegative_kernel_pole_add_remainder_nonneg
    H hH n hn hsupp zeroSum hEF
  linarith

end
end KernelEsmeralda
