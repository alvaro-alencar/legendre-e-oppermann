import Mathlib.Analysis.Complex.Basic
import KernelEsmeralda.EmeraldMinorant

namespace KernelEsmeralda

noncomputable section

def emeraldWeilTest (K : Real → Real) (u : Real) : Complex :=
  (emeraldTilt K u : Complex)

theorem emeraldWeilTest_contDiff_two
    (K : Real → Real) (hK : ContDiff Real ∞ K) :
    ContDiff Real 2 (emeraldWeilTest K) := by
  have ht := emeraldTilt_contDiff_two K hK
  change ContDiff Real 2 (fun u : Real => Complex.ofRealCLM (emeraldTilt K u))
  exact ht.continuousLinearMap_comp Complex.ofRealCLM

end
end KernelEsmeralda
