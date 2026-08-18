import KernelEsmeralda.ExplicitLogTarget
import KernelEsmeralda.ZetaLineSplit

namespace KernelEsmeralda

noncomputable section

/-- Fully concrete Legendre reduction with the zeta contribution separated into
critical-line and off-critical-line blocks.  No zero-location hypothesis is used:
this is only an exact decomposition of the actual zeta explicit formula. -/
theorem legendre_of_split_emerald_remainder
    (n : Nat) (hn : 2 ≤ n)
    (hrem : primePowerLogBarrier n - (n : Real) <
      (emeraldGammaTerm (emeraldTaperWeight n)).re -
        (emeraldZetaOnLineZeroSum (emeraldTaperWeight n)).re -
        (emeraldZetaOffLineZeroSum (emeraldTaperWeight n)).re) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hK3 := emeraldTaperWeight_contDiff_three n hn1
  have hK2 : ContDiff Real 2 (emeraldTaperWeight n) := hK3.of_le (by norm_num)
  have hKcompact := emeraldTaperWeight_hasCompactSupport n hn1
  have hsplit := emeraldZetaZeroSum_eq_onLine_add_offLine
    (emeraldTaperWeight n) hK2 hKcompact
  apply legendre_of_explicit_emerald_taper_log_remainder n hn
  unfold emeraldSpectralRemainder
  rw [hsplit]
  change primePowerLogBarrier n - (n : Real) <
    (emeraldGammaTerm (emeraldTaperWeight n)).re -
      ((emeraldZetaOnLineZeroSum (emeraldTaperWeight n)).re +
       (emeraldZetaOffLineZeroSum (emeraldTaperWeight n)).re)
  linarith

end
end KernelEsmeralda
