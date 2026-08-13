import Mathlib.Analysis.Complex.Basic
import KernelEsmeralda.EmeraldMinorant

namespace KernelEsmeralda

noncomputable section

def emeraldWeilTest (K : Real → Real) (u : Real) : Complex :=
  (emeraldTilt K u : Complex)

end
end KernelEsmeralda
