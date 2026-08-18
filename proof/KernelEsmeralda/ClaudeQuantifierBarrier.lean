import KernelEsmeralda.ClaudeLambdaThreshold

namespace KernelEsmeralda

noncomputable section

/-- Quantifier barrier for the direct Zeta23-to-Legendre support route.

For every single fixed valid paper parameter with `lambda < 1`, there is a
finite threshold after which that fixed lambda lies strictly below the
minimum normalized bandwidth required to reach the Legendre logarithmic
window at square spectral scale.

Thus any direct square-scale use of the Zeta23 support geometry for all large
`n` must let the bandwidth parameter depend on `n` and approach the endpoint
`1`; no fixed `lambda < 1` can suffice. -/
theorem exists_fixed_lambda_below_emerald_min_eventually
    (P : Zeta23.Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∃ N : Nat, 2 ≤ N ∧ ∀ n : Nat, N ≤ n →
      P.lam < emeraldClaudeLambdaMin n := by
  obtain ⟨N, hN2, hmiss⟩ :=
    exists_zeta23_fixed_lambda_square_scale_threshold P hP hlam
  refine ⟨N, hN2, ?_⟩
  intro n hnN
  have hn2 : 2 ≤ n := le_trans hN2 hnN
  have hLlt := hmiss n hnN
  have hnotReach :
      ¬ emeraldLogLeft n ≤ P.L (2 * Real.pi * upperSquare n) :=
    not_le.mpr hLlt
  have hiff := zeta23_square_scale_reaches_left_iff P n hn2
  have hnotMin : ¬ emeraldClaudeLambdaMin n ≤ P.lam := by
    intro hmin
    exact hnotReach (hiff.mpr hmin)
  exact lt_of_not_ge hnotMin

end
end KernelEsmeralda
