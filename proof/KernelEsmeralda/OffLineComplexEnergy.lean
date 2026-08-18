import KernelEsmeralda.GammaOfGeometry
import KernelEsmeralda.ImaginaryPhiDepthQuantitative
import KernelEsmeralda.Zeta23Bridge

namespace KernelEsmeralda

noncomputable section

/-- A zero on the left half of the critical strip forces a quantitative
positive complex-Poisson energy.  The horizontal displacement `1/2 - beta`
becomes imaginary depth in `gammaOf`, and the taper plateau yields an
exponential lower bound for the energy limit. -/
theorem zeta_zero_left_half_complex_energy_lower
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (hre : (rho : Complex).re ≤ 1 / 2) :
    P.L T *
        ((P.w / 2) *
          Real.exp
            ((1 - 2 * (rho : Complex).re) *
              (P.L T / 2 - 3 * P.w / 2))) ≤
      P.L T *
        (P.Phi T
          (Complex.I *
            ((2 * (Zeta23.gammaOf (rho : Complex)).im : Real) : Complex))).re := by
  have hw : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hy : 0 ≤ 2 * (Zeta23.gammaOf (rho : Complex)).im := by
    have hdepth := zeta23_gammaOf_im_nonneg_of_re_le_half (rho : Complex) hre
    linarith
  have hphi := zeta23_taper_Phi_imag_re_ge_edge
    (hϱ := hP.taper) (hw := hw) (hwL := hwL) (hy := hy)
      (L := P.L T) (w := P.w)
      (y := 2 * (Zeta23.gammaOf (rho : Complex)).im)
  have hphiP :
      (P.w / 2) *
          Real.exp
            ((2 * (Zeta23.gammaOf (rho : Complex)).im) *
              (P.L T / 2 - 3 * P.w / 2)) ≤
        (P.Phi T
          (Complex.I *
            ((2 * (Zeta23.gammaOf (rho : Complex)).im : Real) : Complex))).re := by
    change
      (P.w / 2) *
          Real.exp
            ((2 * (Zeta23.gammaOf (rho : Complex)).im) *
              (P.L T / 2 - 3 * P.w / 2)) ≤
        (Zeta23.Taper.Phi P.ϱ (P.L T) P.w
          (Complex.I *
            ((2 * (Zeta23.gammaOf (rho : Complex)).im : Real) : Complex))).re
    exact hphi
  have hmul := mul_le_mul_of_nonneg_left hphiP hL.le
  have hyid :
      2 * (Zeta23.gammaOf (rho : Complex)).im =
        1 - 2 * (rho : Complex).re := by
    rw [zeta23_gammaOf_im_eq_half_sub_re]
    ring
  rw [hyid] at hmul
  rw [hyid]
  exact hmul

/-- The same lower bound is the actual sum of the nonnegative lattice energy,
by the now-proved complex Poisson identity. -/
theorem zeta_zero_left_half_complex_energy_hasSum
    (P : Zeta23.Params) (T : Real)
    (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
    (rho : Zeta23.zetaZeroConfig.carrier) :
    HasSum
      (fun k : Int =>
        Complex.normSq
          (P.phiHat T
            (Zeta23.gammaOf (rho : Complex) -
              (P.tau T k : Complex))))
      (P.L T *
        (P.Phi T
          (Complex.I *
            ((2 * (Zeta23.gammaOf (rho : Complex)).im : Real) : Complex))).re) := by
  exact zeta23ComplexPoisson_energy P T hP hwL
    (Zeta23.gammaOf (rho : Complex))

end
end KernelEsmeralda