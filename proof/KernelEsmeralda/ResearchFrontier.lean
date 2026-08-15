import KernelEsmeralda.CriticalLineLogLoss
import KernelEsmeralda.CriticalLineProductScale
import KernelEsmeralda.BandwidthTwoTarget
import KernelEsmeralda.CriticalLineBandwidthThreshold
import KernelEsmeralda.CriticalLineFrequency

open scoped BigOperators

namespace KernelEsmeralda

noncomputable section

/-- The certified geometric frontier of the current Emerald/Claude route.

At the natural difficult zero height `T = n`, the Emerald phase lies just above
normalized bandwidth two.  At the product height `T = n(n+1)`, the same phase
has normalized frequency exactly one.  The excess above two at natural scale
is explicitly at most `1/(n log n)`.

This theorem is purely geometric.  It does not assume or manufacture a
pair-correlation theorem at bandwidth two. -/
theorem emeraldResearchFrontier_geometry
    (n : Nat) (hn : 2 ≤ n) :
    2 < emeraldTaperCenter n / Real.log (n : Real) ∧
    emeraldTaperCenter n / Real.log (n : Real) - 2 ≤
      1 / ((n : Real) * Real.log (n : Real)) ∧
    emeraldTaperCenter n /
      Real.log ((n : Real) * (((n + 1 : Nat) : Real))) = 1 := by
  exact ⟨two_lt_emeraldNaturalFrequency n hn,
    emeraldNaturalFrequency_sub_two_le n hn,
    emeraldNormalizedFrequency_eq_one_at_product_height n hn⟩

/-- The quantitative companion to `emeraldResearchFrontier_geometry`.

The same magnitude-only critical-line machinery gives two very different
scales:

* on the natural dyadic block `(n,2n]`, only an `O(n log n)` bound;
* on the bandwidth-one transition block `(n(n+1),2n(n+1)]`, an `O(log(n(n+1)))`
  bound.

Thus the remaining logarithmic loss occurs precisely before the phase has
moved into the bandwidth-one regime. -/
theorem exists_emeraldResearchFrontier_bounds :
    ∃ Dnat Tnat Dprod Tprod : Real,
      0 ≤ Dnat ∧ 0 ≤ Dprod ∧
      (∀ (n : Nat), 1 ≤ n → Tnat ≤ (n : Real) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          (n : Real) < (rho : Complex).im ∧
          (rho : Complex).im ≤ 2 * (n : Real)) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          Dnat * (n : Real) * Real.log (n : Real)) ∧
      (∀ (n : Nat), 1 ≤ n →
        Tprod ≤ (n : Real) * (((n + 1 : Nat) : Real)) →
        ∀ (s : Finset Zeta23.zetaZeroConfig.carrier),
        (∀ rho ∈ s,
          (rho : Complex).re = 1 / 2 ∧
          (n : Real) * (((n + 1 : Nat) : Real)) < (rho : Complex).im ∧
          (rho : Complex).im ≤
            2 * ((n : Real) * (((n + 1 : Nat) : Real)))) →
        ‖∑ rho ∈ s, emeraldCriticalExplicitTerm n rho‖ ≤
          Dprod * Real.log ((n : Real) * (((n + 1 : Nat) : Real)))) := by
  obtain ⟨Dnat, Tnat, hDnat, hnat⟩ :=
    exists_emeraldCriticalNaturalScaleLogBound
  obtain ⟨Dprod, Tprod, hDprod, hprod⟩ :=
    exists_emeraldCriticalProductScaleLogBound
  exact ⟨Dnat, Tnat, Dprod, Tprod, hDnat, hDprod, hnat, hprod⟩

/-- Every valid Zeta23 paper parameter remains below the natural Emerald
frequency.  Together with the frontier theorems above, this records why the
current unconditional bandwidth-one certificate does not directly control
the natural Legendre phase. -/
theorem emeraldResearchFrontier_zeta23_gap
    (P : Zeta23.Params) (hP : P.Valid)
    (n : Nat) (hn : 2 ≤ n) :
    P.lam < emeraldTaperCenter n / Real.log (n : Real) :=
  zeta23_lambda_lt_emeraldNaturalFrequency P hP n hn

end
end KernelEsmeralda
