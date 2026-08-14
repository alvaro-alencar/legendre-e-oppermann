import KernelEsmeralda.EmeraldTaper
import KernelEsmeralda.WeilC2Bridge
import KernelEsmeralda.LogSpectralBudget

namespace KernelEsmeralda

noncomputable section

theorem legendre_of_explicit_emerald_taper_log_remainder
    (n : Nat) (hn : 2 ≤ n)
    (hrem : primePowerLogBarrier n - (n : Real) <
      emeraldSpectralRemainder (emeraldTaperWeight n)
        (emeraldZetaZeroSum (emeraldTaperWeight n))) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hK3 := emeraldTaperWeight_contDiff_three n hn1
  have hK2 : ContDiff Real 2 (emeraldTaperWeight n) := hK3.of_le (by norm_num)
  have hKcompact := emeraldTaperWeight_hasCompactSupport n hn1
  have hsupport := emeraldTaperWeight_support n hn1
  have hEF := emeraldExplicitBalance_from_zeta23_of_two
    (emeraldTaperWeight n) hK2 hKcompact
  have hpole : (n : Real) ≤ (emeraldPoleTerm (emeraldTaperWeight n)).re :=
    emeraldPoleTerm_re_linear_core_lower_bound
      (emeraldTaperWeight n) n hn1 hK3.continuous hKcompact
      (emeraldTaperWeight_nonneg n)
      (fun x hx => emeraldTaperWeight_eq_one_on_linear_core n hn1 hx)
  exact legendre_of_log_pole_budget_and_remainder
    (emeraldTaperWeight n) n hn
    (emeraldTaperWeight_le_one n) hsupport
    (emeraldZetaZeroSum (emeraldTaperWeight n)) hEF hpole hrem

end
end KernelEsmeralda
