import KernelEsmeralda.ZetaPairBlockFrobenius
import KernelEsmeralda.DeepRetainedEnergyCost

namespace KernelEsmeralda

noncomputable section

/-- Every deep retained reflection pair has a large individual real Frobenius
self-pairing.  This is the exact matrix version of the scalar `9/8 L⁴`
hyperbolic energy certificate. -/
theorem zetaDeepRetainedLeftPair_realFrobPairing_self_lower
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    (Zeta23.zetaZeroConfig.mult rho : ℝ) ^ 2 *
        (9 / 8 * (P.L T) ^ 4) ≤
      realFrobPairing
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaRealHyperbolicPairBlock P T rho) := by
  dsimp
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hcost := zetaDeepRetainedLeftPair_hyperbolic_energy_cost
    T P hP hwL hT hconj z hz
  have hm0 : 0 ≤ (Zeta23.zetaZeroConfig.mult rho : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcost hm0
  rw [realFrobPairing_zeta_pair_block_self P T rho]
  simpa [rho, mul_assoc] using hmul

/-- Since every zero multiplicity is at least one, a deep retained pair pays
at least `9/8 L⁴` even if multiplicity information is discarded. -/
theorem zetaDeepRetainedLeftPair_realFrobPairing_self_lower_unweighted
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    let rho := zetaCarrierOfZI T z
    9 / 8 * (P.L T) ^ 4 ≤
      realFrobPairing
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaRealHyperbolicPairBlock P T rho) := by
  dsimp
  let rho : Zeta23.zetaZeroConfig.carrier := zetaCarrierOfZI T z
  have hweighted :=
    zetaDeepRetainedLeftPair_realFrobPairing_self_lower
      T P hP hwL hT hconj z hz
  have hm1Nat := Zeta23.zetaZeroConfig.one_le_mult (rho : Complex) rho.property
  have hm1 : (1 : ℝ) ≤ Zeta23.zetaZeroConfig.mult rho := by
    exact_mod_cast hm1Nat
  have hmSq : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult rho : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((Zeta23.zetaZeroConfig.mult rho : ℝ) - 1)]
  have hL4 : 0 ≤ 9 / 8 * (P.L T) ^ 4 := by positivity
  have hscale :
      9 / 8 * (P.L T) ^ 4 ≤
        (Zeta23.zetaZeroConfig.mult rho : ℝ) ^ 2 *
          (9 / 8 * (P.L T) ^ 4) := by
    nlinarith
  exact hscale.trans (by simpa [rho] using hweighted)

end
end KernelEsmeralda
