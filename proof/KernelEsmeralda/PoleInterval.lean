import KernelEsmeralda.PolePositive

open Set

namespace KernelEsmeralda

noncomputable section

theorem emeraldInterval_le_global_exp_weight
    (K : Real → Real) (a b : Real) (hab : a ≤ b)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ u : Real, 0 ≤ K u)
    (hKone : ∀ x ∈ Icc a b, K x = 1) :
    Real.exp b - Real.exp a ≤ ∫ u : Real, Real.exp u * K u := by
  have hint : MeasureTheory.Integrable (fun u : Real => Real.exp u * K u) :=
    emeraldExpWeight_integrable K hKcont hKcompact
  have hnonneg : ∀ u : Real, 0 ≤ Real.exp u * K u := fun u =>
    mul_nonneg (Real.exp_nonneg u) (hKnonneg u)
  have hle :
      (∫ u in Ioc a b, Real.exp u * K u) ≤
        ∫ u : Real, Real.exp u * K u :=
    MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall hnonneg)
  have hinterval :
      (∫ u in a..b, Real.exp u * K u) = Real.exp b - Real.exp a := by
    calc
      (∫ u in a..b, Real.exp u * K u) = ∫ u in a..b, Real.exp u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hab] at hu
        change Real.exp u * K u = Real.exp u
        rw [hKone u hu, mul_one]
      _ = Real.exp b - Real.exp a := by simp
  rw [intervalIntegral.integral_of_le hab] at hinterval
  rw [hinterval] at hle
  exact hle

theorem emeraldPoleTerm_re_interval_lower_bound
    (K : Real → Real) (a b : Real) (hab : a ≤ b)
    (hKcont : Continuous K) (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ u : Real, 0 ≤ K u)
    (hKone : ∀ x ∈ Icc a b, K x = 1) :
    Real.exp b - Real.exp a ≤ (emeraldPoleTerm K).re := by
  have hneg :=
    emeraldInterval_le_global_exp_weight K a b hab hKcont hKcompact hKnonneg hKone
  rw [← emeraldPaperFT_neg_pole_re K] at hneg
  have hpos := emeraldPaperFT_pos_pole_re_nonneg K hKnonneg
  unfold emeraldPoleTerm
  change Real.exp b - Real.exp a ≤
    (emeraldPaperFT K (Complex.I / 2)).re +
      (emeraldPaperFT K (-Complex.I / 2)).re
  linarith

end
end KernelEsmeralda
