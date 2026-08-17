import KernelEsmeralda.ImPartTrace
import KernelEsmeralda.FiniteImaginaryEnergy
import Zeta23.Taper

noncomputable section

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

/-- For the actual Zeta23 block data, the negative PSD trace is exactly the
multiplicity-weighted finite imaginary energy of one representative from each
off-line reflection pair. -/
theorem rtrace_zeta_imPart_eq_weighted_finiteImaginaryEnergy
    (Z : Zeta23.ZeroConfig) (T : ℝ) (P : Zeta23.Params)
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (R : (Zeta23.ZeroSide.blockData Z T P hconj).PairReps) :
    rtrace ((Zeta23.ZeroSide.blockData Z T P hconj).imPart R) =
      ∑ z ∈ R.R,
        (Z.mult z : ℝ) *
          finiteImaginaryEnergy P T (Zeta23.gammaOf (z : ℂ)) := by
  rw [rtrace_imPart_eq_imaginary_energy
    (Zeta23.ZeroSide.blockData Z T P hconj) R]
  refine sum_congr rfl fun z hz => ?_
  simp only [Zeta23.ZeroSide.blockData, Zeta23.ZeroSide.mkData_m]
  unfold finiteImaginaryEnergy Zeta23.ZeroSide.evalVec
  ring

end KernelEsmeralda