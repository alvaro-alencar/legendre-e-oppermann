import KernelEsmeralda.LeftPairReps

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The concrete good-pair predicate used by the off-line imaginary-energy
certificate.  It asks only for the three genuinely quantitative properties
that remain after choosing the left member of each reflection pair:
interiority, sufficient horizontal depth, and small finite-compression loss. -/
def EmeraldDeepRetainedPair
    (T : ℝ) (P : Zeta23.Params)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) : Prop :=
  T + Zeta23.D0 T ≤ (z : Complex).im ∧
  (z : Complex).im ≤ 2 * T - Zeta23.D0 T ∧
  2 * P.L T ≤
    (P.w / 2) * Real.exp
      ((1 - 2 * (z : Complex).re) *
        (P.L T / 2 - 3 * P.w / 2)) ∧
  zetaNaturalCompressionTail P T (zetaCarrierOfZI T z) ≤
    (P.L T) ^ 2 / 2

/-- The finite set of left-half reflection representatives whose individual
imaginary-energy certificate is already strong enough for the deep-pair
argument. -/
def zetaDeepRetainedLeftPairs
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :=
  (zetaLeftPairReps T P hconj).R.filter
    (EmeraldDeepRetainedPair T P)

@[simp] theorem mem_zetaDeepRetainedLeftPairs_iff
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :
    z ∈ zetaDeepRetainedLeftPairs T P hconj ↔
      z ∈ (zetaLeftPairReps T P hconj).R ∧
        EmeraldDeepRetainedPair T P z := by
  simp [zetaDeepRetainedLeftPairs]

/-- The full negative `imPart` trace automatically dominates `L²/2` times the
multiplicity mass of all currently certifiable deep retained off-line pairs.
No condition is imposed on the other off-line pairs. -/
theorem rtrace_zeta_imPart_ge_deepRetainedLeftPair_mass
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    (∑ z ∈ zetaDeepRetainedLeftPairs T P hconj,
        (Zeta23.zetaZeroConfig.mult z : ℝ)) *
        ((P.L T) ^ 2 / 2) ≤
      rtrace ((Zeta23.ZeroSide.blockData
        Zeta23.zetaZeroConfig T P hconj).imPart
          (zetaLeftPairReps T P hconj)) := by
  apply rtrace_zeta_imPart_ge_half_L_sq_mul_deep_subset_mass
    T P hP hwL hT hconj (zetaLeftPairReps T P hconj)
    (zetaDeepRetainedLeftPairs T P hconj)
  · exact Finset.filter_subset _ _
  · intro z hz
    have hzR : z ∈ (zetaLeftPairReps T P hconj).R :=
      (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.1
    exact zetaLeftPairReps_re_le_half T P hconj z hzR
  · intro z hz
    exact (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.2.1
  · intro z hz
    exact (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.2.2.1
  · intro z hz
    exact (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.2.2.2.1
  · intro z hz
    exact (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.2.2.2.2

end
end KernelEsmeralda
