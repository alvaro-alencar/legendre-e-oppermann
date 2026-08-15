import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace KernelEsmeralda

noncomputable section

/-- A coarse consequence of the concrete Riemann--von Mangoldt theorem:
for all sufficiently large T, the multiplicity-weighted number of nontrivial
zeta zeros in (T,2T] is O(T log T). -/
theorem exists_zeta_dyadic_count_upper :
    ∃ B T₀ : Real, 0 < B ∧
      ∀ T : Real, T₀ ≤ T →
        (Zeta23.zetaZeroConfig.N T (2 * T) : Real) ≤ B * T * Real.log T := by
  have hRvM := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  obtain ⟨C, T₁, hmain⟩ := hRvM.main
  let T₀ : Real := max T₁ (Real.exp 1)
  let B : Real := 1 + |C|
  refine ⟨B, T₀, ?_, ?_⟩
  · unfold B
    nlinarith [abs_nonneg C]
  · intro T hT
    have hT1 : T₁ ≤ T := le_trans (le_max_left _ _) hT
    have hexp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hexp
    have hlog1 : 1 ≤ Real.log T := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hexp
    have hlog0 : 0 ≤ Real.log T := le_trans zero_le_one hlog1
    have hpi1 : (1 : Real) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    have hden1 : (1 : Real) ≤ 2 * Real.pi := by nlinarith
    have hdiv : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity : (0 : Real) < 2 * Real.pi)]
      nlinarith
    have hdivpos : 0 < T / (2 * Real.pi) := div_pos hTpos (by positivity)
    have hlogdiv : Real.log (T / (2 * Real.pi)) ≤ Real.log T :=
      Real.log_le_log hdivpos hdiv
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
      norm_num at h ⊢
      exact h
    have hell : Zeta23.ell1 T ≤ 2 * Real.log T := by
      unfold Zeta23.ell1 Zeta23.l
      linarith
    have hmainterm_nonneg : 0 ≤ T / (2 * Real.pi) := le_of_lt hdivpos
    have hmainterm :
        T / (2 * Real.pi) * Zeta23.ell1 T ≤ T * Real.log T := by
      calc
        T / (2 * Real.pi) * Zeta23.ell1 T
            ≤ T / (2 * Real.pi) * (2 * Real.log T) :=
              mul_le_mul_of_nonneg_left hell hmainterm_nonneg
        _ = (T / Real.pi) * Real.log T := by ring
        _ ≤ T * Real.log T := by
          apply mul_le_mul_of_nonneg_right _ hlog0
          rw [div_le_iff₀ (by positivity : (0 : Real) < Real.pi)]
          nlinarith
    have herr := hmain T hT1
    have herr' :
        |(Zeta23.zetaZeroConfig.N T (2 * T) : Real) -
          T / (2 * Real.pi) * Zeta23.ell1 T| ≤ |C| * Real.log T := by
      exact herr.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
    have hN :
        (Zeta23.zetaZeroConfig.N T (2 * T) : Real) ≤
          T / (2 * Real.pi) * Zeta23.ell1 T + |C| * Real.log T := by
      have hleft := le_abs_self
        ((Zeta23.zetaZeroConfig.N T (2 * T) : Real) -
          T / (2 * Real.pi) * Zeta23.ell1 T)
      linarith
    calc
      (Zeta23.zetaZeroConfig.N T (2 * T) : Real)
          ≤ T / (2 * Real.pi) * Zeta23.ell1 T + |C| * Real.log T := hN
      _ ≤ T * Real.log T + |C| * Real.log T := by linarith
      _ ≤ T * Real.log T + |C| * (T * Real.log T) := by
        have hscale : Real.log T ≤ T * Real.log T := by
          exact mul_le_mul_of_nonneg_right (by linarith : (1 : Real) ≤ T) hlog0
        exact add_le_add_left (mul_le_mul_of_nonneg_left hscale (abs_nonneg C)) _
      _ = B * T * Real.log T := by
        unfold B
        ring

end
end KernelEsmeralda
