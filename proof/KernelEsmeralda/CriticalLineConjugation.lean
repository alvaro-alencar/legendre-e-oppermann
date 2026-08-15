import Zeta23.ZetaReflect
import Zeta23.Taper.Fourier
import KernelEsmeralda.CriticalLinePhase
import KernelEsmeralda.CriticalLineWindowBound

open Complex
open scoped ComplexConjugate

namespace KernelEsmeralda

noncomputable section

private theorem nontrivialZero_ne_one {rho : Complex}
    (hrho : Zeta23.IsNontrivialZero rho) : rho ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith [hrho.2.2]

theorem isNontrivialZero_conj {rho : Complex}
    (hrho : Zeta23.IsNontrivialZero rho) :
    Zeta23.IsNontrivialZero (conj rho) := by
  have hne : rho ≠ 1 := nontrivialZero_ne_one hrho
  constructor
  · rw [Zeta23.riemannZeta_conj hne, hrho.1]
    simp
  · simpa using hrho.2.1
  · simpa using hrho.2.2

theorem zeroMult_conj_of_nontrivial {rho : Complex}
    (hrho : Zeta23.IsNontrivialZero rho) :
    Zeta23.zeroMult (conj rho) = Zeta23.zeroMult rho := by
  unfold Zeta23.zeroMult
  rw [Zeta23.analyticOrderAt_zeta_conj (nontrivialZero_ne_one hrho)]

/-- Conjugation as an actual involution of Mathlib-backed nontrivial zeta zeros. -/
def emeraldConjZero (rho : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zetaZeroConfig.carrier := by
  refine ⟨conj (rho : Complex), ?_⟩
  rw [Zeta23.zetaZeroConfig_carrier]
  have hrho : Zeta23.IsNontrivialZero (rho : Complex) := by
    simpa [Zeta23.zetaZeroConfig_carrier] using rho.property
  exact isNontrivialZero_conj hrho

@[simp] theorem emeraldConjZero_val
    (rho : Zeta23.zetaZeroConfig.carrier) :
    ((emeraldConjZero rho : Zeta23.zetaZeroConfig.carrier) : Complex) =
      conj (rho : Complex) := rfl

@[simp] theorem emeraldConjZero_involutive
    (rho : Zeta23.zetaZeroConfig.carrier) :
    emeraldConjZero (emeraldConjZero rho) = rho := by
  apply Subtype.ext
  simp [emeraldConjZero]

@[simp] theorem emeraldConjZero_mult
    (rho : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zetaZeroConfig.mult (emeraldConjZero rho) =
      Zeta23.zetaZeroConfig.mult rho := by
  have hrho : Zeta23.IsNontrivialZero (rho : Complex) := by
    simpa [Zeta23.zetaZeroConfig_carrier] using rho.property
  change Zeta23.zeroMult (conj (rho : Complex)) = Zeta23.zeroMult (rho : Complex)
  exact zeroMult_conj_of_nontrivial hrho

@[simp] theorem emeraldConjZero_re
    (rho : Zeta23.zetaZeroConfig.carrier) :
    ((emeraldConjZero rho : Zeta23.zetaZeroConfig.carrier) : Complex).re =
      (rho : Complex).re := by simp [emeraldConjZero]

@[simp] theorem emeraldConjZero_im
    (rho : Zeta23.zetaZeroConfig.carrier) :
    ((emeraldConjZero rho : Zeta23.zetaZeroConfig.carrier) : Complex).im =
      -(rho : Complex).im := by simp [emeraldConjZero]

theorem emerald_phiHat_conj_zero
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (emeraldConjZero rho : Complex)) =
      conj (Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
        (emeraldTaperLength n) (emeraldTaperWidth n)
        (-Complex.I * (rho : Complex))) := by
  have h := Zeta23.Taper.conj_paperFT_ofReal
    (Zeta23.Taper.phi Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n))
    (-Complex.I * (rho : Complex))
  change conj (Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n)
      (-Complex.I * (rho : Complex))) =
    Zeta23.Taper.phiHat Zeta23.Taper.smoothstep
      (emeraldTaperLength n) (emeraldTaperWidth n)
      (-conj (-Complex.I * (rho : Complex))) at h
  rw [← h]
  congr 1
  simp [emeraldConjZero]

theorem emerald_exp_conj_zero
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier) :
    Complex.exp ((emeraldConjZero rho : Complex) *
        (emeraldTaperCenter n : Complex)) =
      conj (Complex.exp ((rho : Complex) *
        (emeraldTaperCenter n : Complex))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [emeraldConjZero]

theorem emeraldCriticalExplicitTerm_conj
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier) :
    emeraldCriticalExplicitTerm n (emeraldConjZero rho) =
      conj (emeraldCriticalExplicitTerm n rho) := by
  unfold emeraldCriticalExplicitTerm
  rw [emeraldConjZero_mult, emerald_exp_conj_zero,
    emerald_phiHat_conj_zero]
  simp

/-- A conjugate pair contributes a real number, namely twice the real part
of either member's oscillatory term. -/
theorem emeraldCriticalExplicitTerm_pair
    (n : Nat) (rho : Zeta23.zetaZeroConfig.carrier) :
    emeraldCriticalExplicitTerm n rho +
        emeraldCriticalExplicitTerm n (emeraldConjZero rho) =
      (2 * (emeraldCriticalExplicitTerm n rho).re : Real) := by
  rw [emeraldCriticalExplicitTerm_conj]
  apply Complex.ext
  · simp
    ring
  · simp

end
end KernelEsmeralda
