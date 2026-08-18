import KernelEsmeralda.OffLineRayleighInterference
import KernelEsmeralda.DeepRetainedPairCorrelations

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Interference contributed by the reflection pair represented by `s` along
the imaginary direction attached to `rho`. -/
def zetaImagRayPairInterference
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (s : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) : ℝ :=
  (Zeta23.zetaZeroConfig.mult (zetaCarrierOfZI T s) : ℝ) / 2 *
    (finiteImagRealCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf ((zetaCarrierOfZI T s :
          Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2 -
      finiteImagImagCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf ((zetaCarrierOfZI T s :
          Zeta23.zetaZeroConfig.carrier) : Complex)) ^ 2)

/-- Left representatives not currently certified as deep and retained.  These
are precisely the shallow/boundary/compression-loss exceptions for the present
argument. -/
def zetaExceptionalLeftPairs
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Finset (Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T) :=
  (zetaLeftPairReps T P hconj).R \ zetaDeepRetainedLeftPairs T P hconj

/-- The deep and exceptional populations are disjoint. -/
theorem disjoint_deepRetained_exceptional
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    Disjoint
      (zetaDeepRetainedLeftPairs T P hconj)
      (zetaExceptionalLeftPairs T P hconj) := by
  unfold zetaExceptionalLeftPairs
  exact Finset.disjoint_sdiff_right

/-- Deep retained pairs together with the exceptional remainder recover all
canonical left representatives. -/
theorem deepRetained_union_exceptional_eq_leftReps
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P) :
    zetaDeepRetainedLeftPairs T P hconj ∪
        zetaExceptionalLeftPairs T P hconj =
      (zetaLeftPairReps T P hconj).R := by
  ext s
  simp [zetaExceptionalLeftPairs, zetaDeepRetainedLeftPairs]
  tauto

/-- After removing a selected deep pair `z`, the remaining left representatives
split exactly into the other deep retained pairs and the exceptional remainder. -/
theorem erase_leftReps_eq_deep_erase_union_exceptional
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    (zetaLeftPairReps T P hconj).R.erase z =
      (zetaDeepRetainedLeftPairs T P hconj).erase z ∪
        zetaExceptionalLeftPairs T P hconj := by
  ext s
  have hzR : z ∈ (zetaLeftPairReps T P hconj).R :=
    (mem_zetaDeepRetainedLeftPairs_iff T P hconj z).mp hz |>.1
  constructor
  · intro hs
    have hsR : s ∈ (zetaLeftPairReps T P hconj).R :=
      (Finset.mem_erase.mp hs).2
    have hsz : s ≠ z := (Finset.mem_erase.mp hs).1
    by_cases hd : s ∈ zetaDeepRetainedLeftPairs T P hconj
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hsz, hd⟩)
    · exact Finset.mem_union_right _ (by
        simp [zetaExceptionalLeftPairs, hsR, hd])
  · intro hs
    rcases Finset.mem_union.mp hs with hd | he
    · have hdm := Finset.mem_erase.mp hd
      have hdR : s ∈ (zetaLeftPairReps T P hconj).R :=
        (mem_zetaDeepRetainedLeftPairs_iff T P hconj s).mp hdm.2 |>.1
      exact Finset.mem_erase.mpr ⟨hdm.1, hdR⟩
    · have he' := Finset.mem_sdiff.mp he
      have hsz : s ≠ z := by
        intro h
        subst s
        exact he'.2 hz
      exact Finset.mem_erase.mpr ⟨hsz, he'.1⟩

/-- The off-diagonal cancellation budget splits into a controlled deep-deep
part and an explicit exceptional part. -/
theorem zetaDeepRetainedLeftPair_interference_split
    (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    (∑ s ∈ (zetaLeftPairReps T P hconj).R.erase z,
        zetaImagRayPairInterference P T rho s) =
      (∑ s ∈ (zetaDeepRetainedLeftPairs T P hconj).erase z,
          zetaImagRayPairInterference P T rho s) +
        ∑ s ∈ zetaExceptionalLeftPairs T P hconj,
          zetaImagRayPairInterference P T rho s := by
  dsimp
  rw [erase_leftReps_eq_deep_erase_union_exceptional T P hconj z hz]
  rw [Finset.sum_union]
  have hdisj := disjoint_deepRetained_exceptional T P hconj
  exact hdisj.mono_left (Finset.erase_subset _ _)

/-- Full off-line Rayleigh decomposition for a deep retained pair: self term,
other deep retained pairs, and the exceptional remainder. -/
theorem zetaDeepRetainedLeftPair_offLineRayleigh_three_way_split
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let R := zetaLeftPairReps T P hconj
    let rho := zetaCarrierOfZI T z
    realQuadraticForm
        (zetaRealOffLinePairBlockSum P T hconj R)
        (zetaPairImagVector P T rho) =
      realQuadraticForm
          (zetaRealHyperbolicPairBlock P T rho)
          (zetaPairImagVector P T rho) +
        (∑ s ∈ (zetaDeepRetainedLeftPairs T P hconj).erase z,
          zetaImagRayPairInterference P T rho s) +
        ∑ s ∈ zetaExceptionalLeftPairs T P hconj,
          zetaImagRayPairInterference P T rho s := by
  dsimp
  have hsplit := zetaDeepRetainedLeftPair_offLineRayleigh_split
    T P hP hwL hT hconj z hz
  have hinterf := zetaDeepRetainedLeftPair_interference_split
    T P hconj z hz
  dsimp at hsplit hinterf ⊢
  unfold zetaImagRayPairInterference at hinterf
  rw [hsplit, hinterf]
  ring

end
end KernelEsmeralda
