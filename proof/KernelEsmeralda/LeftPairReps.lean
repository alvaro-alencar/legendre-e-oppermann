import KernelEsmeralda.DeepSubsetTrace

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The left-half analogue of Zeta23's canonical pair representatives.
For every off-critical reflection pair, choose the member with real part
strictly below `1/2`. -/
def leftPairRepsForMkData
    {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Zeta23.ZeroConfig) (T : ℝ)
    (v : Zeta23.ZeroSide.ZI Z T → d → ℂ)
    (hv : ∀ z : Zeta23.ZeroSide.ZI Z T,
      v ⟨Zeta23.reflect z,
        Zeta23.ZeroSide.reflect_mem_ZI Z T z.2⟩ = star (v z)) :
    (Zeta23.ZeroSide.mkData Z T v hv).PairReps where
  R := {z | (z : ℂ).re < 1 / 2}
  off z hz h := by
    rw [Zeta23.ZeroSide.mkData_σ_eq_iff] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    linarith
  σ_not_mem z hz h := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Zeta23.ZeroSide.mkData_σ, Zeta23.ZeroSide.reflect_re] at hz h
    linarith
  cover z hz := by
    rw [ne_eq, Zeta23.ZeroSide.mkData_σ_eq_iff] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Zeta23.ZeroSide.mkData_σ, Zeta23.ZeroSide.reflect_re]
    rcases lt_or_gt_of_ne hz with hleft | hright
    · exact Or.inl hleft
    · right
      linarith

/-- Left-half representatives for the actual Mathlib-backed zeta block. -/
def zetaLeftPairReps
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    (Zeta23.ZeroSide.blockData
      Zeta23.zetaZeroConfig T P hconj).PairReps := by
  exact leftPairRepsForMkData
    Zeta23.zetaZeroConfig T
    (Zeta23.ZeroSide.evalVec Zeta23.zetaZeroConfig T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj)

@[simp] theorem mem_zetaLeftPairReps_iff
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :
    z ∈ (zetaLeftPairReps T P hconj).R ↔
      (z : Complex).re < 1 / 2 := by
  rfl

/-- Every chosen left representative is automatically on the weak left half
required by the energy estimates. -/
theorem zetaLeftPairReps_re_le_half
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ (zetaLeftPairReps T P hconj).R) :
    (z : Complex).re ≤ 1 / 2 := by
  exact (mem_zetaLeftPairReps_iff T P hconj z).mp hz |>.le

end
end KernelEsmeralda
