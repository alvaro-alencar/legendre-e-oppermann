import KernelEsmeralda.PaperFTShift
import KernelEsmeralda.ResearchTarget
import KernelEsmeralda.CriticalLineFrequency

namespace KernelEsmeralda

noncomputable section

/-- The local Weil test obtained by moving the left endpoint `log(n^2)` to
zero.  This definition is profile-agnostic. -/
def emeraldLeftShiftedWeilTest
    (K : Real → Real) (n : Nat) (v : Real) : Complex :=
  emeraldWeilTest K (v + emeraldLogLeft n)

/-- Every Emerald Fourier transform carries the exact common phase generated
by the left endpoint of the Legendre logarithmic window.

Thus the global oscillation is not a peculiarity of the smoothstep taper: any
kernel localized in the same interval inherits the factor
`exp(i z log(n^2))`.  All profile freedom is pushed into the short local
transform on the right. -/
theorem emeraldPaperFT_factor_left_edge
    (K : Real → Real) (n : Nat) (z : Complex) :
    emeraldPaperFT K z =
      Complex.exp
        (Complex.I * z * (emeraldLogLeft n : Complex)) *
      Zeta23.paperFT (emeraldLeftShiftedWeilTest K n) z := by
  change Zeta23.paperFT (emeraldWeilTest K) z = _
  simpa [emeraldLeftShiftedWeilTest] using
    (paperFT_translate
      (emeraldLeftShiftedWeilTest K n) (emeraldLogLeft n) z)

/-- If the original weight is supported inside the Legendre logarithmic
window, then after removing the left-edge phase the remaining local Weil test
is supported in a window of width exactly `emeraldTaperLength n` starting at
zero. -/
theorem emeraldLeftShiftedWeilTest_support
    (K : Real → Real) (n : Nat)
    (hsupp : Function.support K ⊆
      Set.Ioo (emeraldLogLeft n) (emeraldLogRight n)) :
    Function.support (emeraldLeftShiftedWeilTest K n) ⊆
      Set.Ioo 0 (emeraldTaperLength n) := by
  intro v hv
  have htest : emeraldLeftShiftedWeilTest K n v ≠ 0 :=
    Function.mem_support.mp hv
  have hKne : K (v + emeraldLogLeft n) ≠ 0 := by
    intro hK0
    apply htest
    simp [emeraldLeftShiftedWeilTest, emeraldWeilTest, emeraldTilt, hK0]
  have hmem := hsupp (Function.mem_support.mpr hKne)
  unfold emeraldTaperLength
  constructor <;> linarith [hmem.1, hmem.2]

/-- At the natural zero height `T=n`, the left-edge phase itself already has
normalized frequency exactly two.  Any center strictly inside the interval
therefore lies above two, independently of the profile. -/
theorem emeraldLeftEdge_normalized_frequency_eq_two
    (n : Nat) (hn : 2 ≤ n) :
    emeraldLogLeft n / Real.log (n : Real) = 2 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hlogne : Real.log (n : Real) ≠ 0 := by
    exact (Real.log_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn))).ne'
  rw [emeraldLogLeft_eq_two_log_n n hn1]
  field_simp [hlogne]

end
end KernelEsmeralda
