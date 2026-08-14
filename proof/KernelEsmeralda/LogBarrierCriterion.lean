import KernelEsmeralda.PrimePowerLogBarrier
import KernelEsmeralda.PrimePowerWindowSqrt

namespace KernelEsmeralda

noncomputable section

theorem legendre_of_emeraldMass_gt_logBarrier
    (K : Real → Real) (hK : ∀ u : Real, K u ≤ 1)
    (n : Nat) (hn : 2 ≤ n)
    (hmass : primePowerLogBarrier n < emeraldMass K n) :
    ∃ p : Nat, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hmassPsi : primePowerLogBarrier n < deltaPsi n :=
    hmass.trans_le (emeraldMass_le_deltaPsi K hK n)
  have hrem := higherPowerRemainderDelta_le_logBarrier n hn
  exact legendre_of_deltaPsi_gt_remainderDelta n (hrem.trans_lt hmassPsi)

end
end KernelEsmeralda
