import KernelEsmeralda.LinearCoreWitness

namespace KernelEsmeralda

noncomputable section

def emeraldSpectralRemainder (K : Real → Real) (zeroSum : Complex) : Real :=
  (emeraldGammaTerm K - zeroSum).re

end
end KernelEsmeralda
