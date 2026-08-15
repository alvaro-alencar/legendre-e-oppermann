import Zeta23.RvM.LocalCount
import Zeta23.Defs.Counting
import KernelEsmeralda.ZetaLineSplit

namespace KernelEsmeralda

noncomputable section

/-- The concrete zeta local-count theorem restricted to critical-line zeros.
The same absolute constant that counts all nontrivial zeros in a unit window
also counts the on-line subfamily, with multiplicity. -/
theorem emeraldCriticalLine_local_count :
    ∃ A₀ : Real, 1 ≤ A₀ ∧ ∀ t : Real,
      (Zeta23.zetaZeroConfig.N0 t (t + 1) : Real) ≤
        A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, ?_⟩
  intro t
  have hsub : Zeta23.zetaZeroConfig.N0 t (t + 1) ≤
      Zeta23.zetaZeroConfig.N t (t + 1) :=
    (Zeta23.zetaZeroConfig.trivial_chain t (t + 1)).2.2.1
  have hsubR :
      (Zeta23.zetaZeroConfig.N0 t (t + 1) : Real) ≤
        (Zeta23.zetaZeroConfig.N t (t + 1) : Real) := by
    exact_mod_cast hsub
  exact hsubR.trans (hloc t)

end
end KernelEsmeralda
