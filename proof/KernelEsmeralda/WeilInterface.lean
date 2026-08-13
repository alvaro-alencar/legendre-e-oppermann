import Mathlib.Analysis.Complex.Basic
import KernelEsmeralda.EmeraldMinorant

open scoped ContDiff

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

theorem emeraldWeilTest_hasCompactSupport
    (K : Real → Real) (hK : HasCompactSupport K) :
    HasCompactSupport (emeraldWeilTest K) := by
  change HasCompactSupport (Complex.ofReal ∘ emeraldTilt K)
  exact (emeraldTilt_hasCompactSupport K hK).comp_left (by simp)

theorem weil_prime_factor_normalization_complex
    (K : Real → Real) (m : Nat) (hm : 0 < m) :
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt (m : Real) : Real) : Complex) *
        emeraldWeilTest K (Real.log (m : Real)) =
      ((ArithmeticFunction.vonMangoldt m * K (Real.log (m : Real)) : Real) : Complex) := by
  simpa [emeraldWeilTest] using
    congrArg (fun x : Real => (x : Complex))
      (weil_prime_factor_normalization K m hm)

end
end KernelEsmeralda
