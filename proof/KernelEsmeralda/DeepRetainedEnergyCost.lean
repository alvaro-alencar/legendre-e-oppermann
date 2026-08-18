import KernelEsmeralda.DeepRetainedFiniteGeometry
import KernelEsmeralda.HyperbolicEnergyCost

namespace KernelEsmeralda

noncomputable section

/-- Every deep retained left representative pays a fixed scalar hyperbolic
energy cost inside the finite Zeta23 compression. -/
theorem zetaDeepRetainedLeftPair_hyperbolic_energy_cost
    (T : ℝ) (P : Zeta23.Params)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (hT : 1 ≤ T)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (z : Zeta23.ZeroSide.ZI Zeta23.zetaZeroConfig T)
    (hz : z ∈ zetaDeepRetainedLeftPairs T P hconj) :
    9 / 8 * (P.L T) ^ 4 ≤
      (finiteRealEnergy P T (Zeta23.gammaOf (z : Complex))) ^ 2 +
      (finiteImaginaryEnergy P T (Zeta23.gammaOf (z : Complex))) ^ 2 -
      2 * (finiteCrossEnergy P T (Zeta23.gammaOf (z : Complex))) ^ 2 := by
  obtain ⟨hEi, hEr, hEc⟩ :=
    zetaDeepRetainedLeftPair_finite_geometry
      T P hP hwL hT hconj z hz
  exact hyperbolic_energy_cost_ge_nine_eighths hEr hEi hEc

end
end KernelEsmeralda
