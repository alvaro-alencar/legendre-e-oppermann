import KernelEsmeralda.WeilPrimeBridge

open Set
open scoped ContDiff

namespace KernelEsmeralda

noncomputable section

def emeraldBarrier (n : Nat) : Real :=
  Real.log (((n + 1 : Nat) : Real)) +
    (Real.log 4 + 4) * (upperSquare n ^ (1 / (3 : Real))) +
    (Real.log 4 + 4) * (upperSquare n ^ (1 / (5 : Real)))

end
end KernelEsmeralda
