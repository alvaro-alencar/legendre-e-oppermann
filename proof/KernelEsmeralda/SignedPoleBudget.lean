import KernelEsmeralda.SignedKernelCorrection
import KernelEsmeralda.LogSpectralBudget
import KernelEsmeralda.PoleReal
import KernelEsmeralda.PoleGlobal

namespace KernelEsmeralda

noncomputable section

/-- Exact real-part formula for the pole contribution. -/
theorem emeraldPoleTerm_re_eq_integrals (K : Real → Real) :
    (emeraldPoleTerm K).re =
      (∫ u : Real, K u) + ∫ u : Real, Real.exp u * K u := by
  unfold emeraldPoleTerm
  rw [Complex.add_re, emeraldPaperFT_pos_pole_re, emeraldPaperFT_neg_pole_re]

/-- For continuous compactly-supported kernels the real pole contribution is
exactly linear under subtraction. -/
theorem emeraldPoleTerm_re_sub
    (K H : Real → Real)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hHcont : Continuous H) (hHcompact : HasCompactSupport H) :
    (emeraldPoleTerm (fun u => K u - H u)).re =
      (emeraldPoleTerm K).re - (emeraldPoleTerm H).re := by
  have hKi : MeasureTheory.Integrable K :=
    hKcont.integrable_of_hasCompactSupport hKcompact
  have hHi : MeasureTheory.Integrable H :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have hKe := emeraldExpWeight_integrable K hKcont hKcompact
  have hHe := emeraldExpWeight_integrable H hHcont hHcompact
  rw [emeraldPoleTerm_re_eq_integrals,
      emeraldPoleTerm_re_eq_integrals K,
      emeraldPoleTerm_re_eq_integrals H]
  have hsub :
      (fun u : Real => Real.exp u * (K u - H u)) =
        fun u : Real => Real.exp u * K u - Real.exp u * H u := by
    funext u
    ring
  rw [MeasureTheory.integral_sub hKi hHi, hsub,
      MeasureTheory.integral_sub hKe hHe]
  ring

/-- General pole-floor version of the logarithmic spectral criterion.  The
existing theorem uses `poleFloor = n`; this version makes the accounting
parameter explicit. -/
theorem legendre_of_log_pole_floor_and_remainder
    (K : Real → Real) (n : Nat) (hn : 2 ≤ n)
    (hKle : ∀ u : Real, K u ≤ 1)
    (hsupp : Function.support K ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (zeroSum : Complex) (hEF : EmeraldExplicitBalance K zeroSum)
    (poleFloor : Real)
    (hpole : poleFloor ≤ (emeraldPoleTerm K).re)
    (hrem : primePowerLogBarrier n - poleFloor <
      emeraldSpectralRemainder K zeroSum) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hre := emeraldMass_eq_spectralBalance_re K n hn hsupp zeroSum hEF
  have hmass : primePowerLogBarrier n < emeraldMass K n := by
    rw [hre]
    unfold emeraldSpectralRemainder at hrem
    change primePowerLogBarrier n - poleFloor <
      (emeraldGammaTerm K).re - zeroSum.re at hrem
    change primePowerLogBarrier n <
      (emeraldPoleTerm K).re + (emeraldGammaTerm K).re - zeroSum.re
    linarith
  exact legendre_of_emeraldMass_gt_logBarrier K hKle n hn hmass

/-- Full spectral bookkeeping for a signed correction `K-H`.  Starting from a
baseline pole floor `n`, if the correction costs at most `B` in real pole
mass, then `n-B` remains available as the main-term floor. -/
theorem legendre_of_signed_correction_spectral_budget
    (K H : Real → Real)
    (hKle : ∀ u : Real, K u ≤ 1)
    (hHnonneg : ∀ u : Real, 0 ≤ H u)
    (hKsupp : Function.support K ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hHsupp : Function.support H ⊆ Set.Ioo (emeraldLogLeft n) (emeraldLogRight n))
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hHcont : Continuous H) (hHcompact : HasCompactSupport H)
    (n : Nat) (hn : 2 ≤ n)
    (B : Real)
    (hbasePole : (n : Real) ≤ (emeraldPoleTerm K).re)
    (hcost : (emeraldPoleTerm H).re ≤ B)
    (zeroSum : Complex)
    (hEF : EmeraldExplicitBalance (fun u => K u - H u) zeroSum)
    (hrem : primePowerLogBarrier n - ((n : Real) - B) <
      emeraldSpectralRemainder (fun u => K u - H u) zeroSum) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hpoleSub := emeraldPoleTerm_re_sub K H hKcont hKcompact hHcont hHcompact
  have hpole : (n : Real) - B ≤
      (emeraldPoleTerm (fun u => K u - H u)).re := by
    rw [hpoleSub]
    linarith
  exact legendre_of_log_pole_floor_and_remainder
    (fun u => K u - H u) n hn
    (sub_nonneg_correction_le_one K H hKle hHnonneg)
    (support_sub_subset_legendre_window K H n hKsupp hHsupp)
    zeroSum hEF ((n : Real) - B) hpole hrem

end
end KernelEsmeralda
