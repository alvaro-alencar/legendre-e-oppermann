import Zeta23.Statement.SeamClosed
import Zeta23.WeilEF.Main
import KernelEsmeralda.SpectralWitness

namespace KernelEsmeralda

noncomputable section

theorem zeta23_explicit_formula_available :
    Zeta23.EF.EF_lit Zeta23.zetaZeroConfig := by
  simpa [Zeta23.zetaZeroConfig] using
    Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam

end
end KernelEsmeralda
