import Zeta23.Assembly

open Matrix Finset RHLinalg
open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Entrywise real Frobenius pairing. -/
def realFrobPairing (A B : Matrix d d ℝ) : ℝ :=
  ∑ i : d, ∑ j : d, A i j * B i j

/-- Doubled Euclidean correlation.  This normalization matches the finite
real/imaginary correlations used for the zero vectors. -/
def doubledDot (x y : d → ℝ) : ℝ :=
  ∑ i : d, 2 * x i * y i

/-- A real hyperbolic reflection-pair block: `2m(xxᵀ - yyᵀ)`. -/
def realHyperbolicPairBlock (m : ℝ) (x y : d → ℝ) : Matrix d d ℝ :=
  (2 * m) • (vecMulVec x x - vecMulVec y y)

/-- Frobenius pairing of two real rank-one symmetric matrices is the square
of the vector dot product. -/
theorem realFrobPairing_vecMulVec_self
    (x u : d → ℝ) :
    realFrobPairing (vecMulVec x x) (vecMulVec u u) =
      (∑ i : d, x i * u i) ^ 2 := by
  unfold realFrobPairing
  simp only [vecMulVec_apply]
  calc
    (∑ i : d, ∑ j : d, (x i * x j) * (u i * u j)) =
        ∑ i : d, ∑ j : d, (x i * u i) * (x j * u j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : d, (x i * u i) * (∑ j : d, x j * u j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = (∑ i : d, x i * u i) * (∑ j : d, x j * u j) := by
      rw [Finset.sum_mul]
    _ = (∑ i : d, x i * u i) ^ 2 := by ring

/-- Entrywise Frobenius pairing is bilinear in the first argument. -/
theorem realFrobPairing_sub_left
    (A B C : Matrix d d ℝ) :
    realFrobPairing (A - B) C =
      realFrobPairing A C - realFrobPairing B C := by
  unfold realFrobPairing
  simp only [Matrix.sub_apply]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

/-- Entrywise Frobenius pairing is bilinear in the second argument. -/
theorem realFrobPairing_sub_right
    (A B C : Matrix d d ℝ) :
    realFrobPairing A (B - C) =
      realFrobPairing A B - realFrobPairing A C := by
  unfold realFrobPairing
  simp only [Matrix.sub_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- Scalar factors pull out of both sides of the Frobenius pairing. -/
theorem realFrobPairing_smul_smul
    (a b : ℝ) (A B : Matrix d d ℝ) :
    realFrobPairing (a • A) (b • B) =
      (a * b) * realFrobPairing A B := by
  unfold realFrobPairing
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i : d, ∑ j : d, (a * A i j) * (b * B i j)) =
        ∑ i : d, ∑ j : d, (a * b) * (A i j * B i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (a * b) * (∑ i : d, ∑ j : d, A i j * B i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Exact cross-pair Frobenius identity.  The factor `4` from the two pair
blocks cancels exactly against the use of doubled correlations. -/
theorem realFrobPairing_hyperbolic_pair_blocks
    (m n : ℝ) (x y u v : d → ℝ) :
    realFrobPairing
        (realHyperbolicPairBlock m x y)
        (realHyperbolicPairBlock n u v) =
      m * n *
        (doubledDot x u ^ 2 + doubledDot y v ^ 2 -
          doubledDot x v ^ 2 - doubledDot y u ^ 2) := by
  unfold realHyperbolicPairBlock
  rw [realFrobPairing_smul_smul]
  rw [realFrobPairing_sub_left, realFrobPairing_sub_right,
    realFrobPairing_sub_right]
  rw [realFrobPairing_vecMulVec_self,
    realFrobPairing_vecMulVec_self,
    realFrobPairing_vecMulVec_self,
    realFrobPairing_vecMulVec_self]
  unfold doubledDot
  have hxu : (∑ i : d, 2 * x i * u i) =
      2 * (∑ i : d, x i * u i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hyv : (∑ i : d, 2 * y i * v i) =
      2 * (∑ i : d, y i * v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hxv : (∑ i : d, 2 * x i * v i) =
      2 * (∑ i : d, x i * v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hyu : (∑ i : d, 2 * y i * u i) =
      2 * (∑ i : d, y i * u i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hxu, hyv, hxv, hyu]
  ring

/-- Diagonal specialization of the cross-pair identity. -/
theorem realFrobPairing_hyperbolic_pair_block_self
    (m : ℝ) (x y : d → ℝ) :
    realFrobPairing
        (realHyperbolicPairBlock m x y)
        (realHyperbolicPairBlock m x y) =
      m ^ 2 *
        (doubledDot x x ^ 2 + doubledDot y y ^ 2 -
          2 * doubledDot x y ^ 2) := by
  rw [realFrobPairing_hyperbolic_pair_blocks]
  have hsym : doubledDot y x = doubledDot x y := by
    unfold doubledDot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsym]
  ring

end
end KernelEsmeralda
