import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Set
import KernelEsmeralda.PoleCore

namespace KernelEsmeralda

noncomputable section

theorem emeraldExpWeight_integrable
    (K : Real → Real) (hKcont : Continuous K) (hKcompact : HasCompactSupport K) :
    MeasureTheory.Integrable (fun u : Real => Real.exp u * K u) := by
  have hcont : Continuous (fun u : Real => Real.exp u * K u) :=
    Real.continuous_exp.mul hKcont
  have hsupp : HasCompactSupport (fun u : Real => Real.exp u * K u) := by
    apply hKcompact.mono
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro hKu
    apply hu
    simp [hKu]
  exact hcont.integrable_of_hasCompactSupport hsupp

end
end KernelEsmeralda
