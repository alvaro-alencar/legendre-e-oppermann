import KernelEsmeralda.PairBlockFrobenius
import KernelEsmeralda.FiniteBilinearGeometry

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- Real part of the finite sampled vector attached to a zeta zero. -/
def zetaPairRealVector
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : Fin (P.d T) → ℝ :=
  fun k =>
    (P.phiHat T
      (Zeta23.gammaOf (rho : Complex) -
        (P.tau T (k : ℤ) : Complex))).re

/-- Imaginary part of the same finite sampled vector. -/
def zetaPairImagVector
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : Fin (P.d T) → ℝ :=
  fun k =>
    (P.phiHat T
      (Zeta23.gammaOf (rho : Complex) -
        (P.tau T (k : ℤ) : Complex))).im

/-- Real hyperbolic matrix carried by one reflection pair representative. -/
def zetaRealHyperbolicPairBlock
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℝ :=
  realHyperbolicPairBlock
    (Zeta23.zetaZeroConfig.mult rho : ℝ)
    (zetaPairRealVector P T rho)
    (zetaPairImagVector P T rho)

/-- The doubled real-real dot product of the two pair vectors is exactly the
finite resolved RR correlation. -/
theorem doubledDot_zetaPairReal_eq_RR
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    doubledDot
        (zetaPairRealVector P T rho)
        (zetaPairRealVector P T sigma) =
      finiteRealRealCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf (sigma : Complex)) := by
  rfl

/-- The doubled imaginary-imaginary dot product is the II correlation. -/
theorem doubledDot_zetaPairImag_eq_II
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    doubledDot
        (zetaPairImagVector P T rho)
        (zetaPairImagVector P T sigma) =
      finiteImagImagCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf (sigma : Complex)) := by
  rfl

/-- Real-imaginary dot product is the RI correlation. -/
theorem doubledDot_zetaPairRealImag_eq_RI
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    doubledDot
        (zetaPairRealVector P T rho)
        (zetaPairImagVector P T sigma) =
      finiteRealImagCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf (sigma : Complex)) := by
  rfl

/-- Imaginary-real dot product is the IR correlation. -/
theorem doubledDot_zetaPairImagReal_eq_IR
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    doubledDot
        (zetaPairImagVector P T rho)
        (zetaPairRealVector P T sigma) =
      finiteImagRealCorrelation P T
        (Zeta23.gammaOf (rho : Complex))
        (Zeta23.gammaOf (sigma : Complex)) := by
  rfl

/-- Exact zeta pair-block Frobenius cross term in terms of the four finite
resolved correlations. -/
theorem realFrobPairing_zeta_pair_blocks
    (P : Zeta23.Params) (T : ℝ)
    (rho sigma : Zeta23.zetaZeroConfig.carrier) :
    realFrobPairing
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaRealHyperbolicPairBlock P T sigma) =
      (Zeta23.zetaZeroConfig.mult rho : ℝ) *
      (Zeta23.zetaZeroConfig.mult sigma : ℝ) *
        (finiteRealRealCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2 +
          finiteImagImagCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2 -
          finiteRealImagCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2 -
          finiteImagRealCorrelation P T
            (Zeta23.gammaOf (rho : Complex))
            (Zeta23.gammaOf (sigma : Complex)) ^ 2) := by
  unfold zetaRealHyperbolicPairBlock
  rw [realFrobPairing_hyperbolic_pair_blocks]
  rw [doubledDot_zetaPairReal_eq_RR,
    doubledDot_zetaPairImag_eq_II,
    doubledDot_zetaPairRealImag_eq_RI,
    doubledDot_zetaPairImagReal_eq_IR]

/-- On the diagonal, the actual zeta pair block recovers the scalar
hyperbolic energy combination already certified for deep retained pairs. -/
theorem realFrobPairing_zeta_pair_block_self
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    realFrobPairing
        (zetaRealHyperbolicPairBlock P T rho)
        (zetaRealHyperbolicPairBlock P T rho) =
      (Zeta23.zetaZeroConfig.mult rho : ℝ) ^ 2 *
        (finiteRealEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 +
          finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2 -
          2 * finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) ^ 2) := by
  rw [realFrobPairing_zeta_pair_blocks]
  have hRR :
      finiteRealRealCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteRealEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    rfl
  have hII :
      finiteImagImagCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteImaginaryEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    rfl
  have hRI :
      finiteRealImagCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    rfl
  have hIR :
      finiteImagRealCorrelation P T
          (Zeta23.gammaOf (rho : Complex))
          (Zeta23.gammaOf (rho : Complex)) =
        finiteCrossEnergy P T (Zeta23.gammaOf (rho : Complex)) := by
    unfold finiteImagRealCorrelation finiteCrossEnergy
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hRR, hII, hRI, hIR]
  ring

end
end KernelEsmeralda
