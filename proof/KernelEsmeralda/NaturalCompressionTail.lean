import KernelEsmeralda.ImaginaryCompressionNaturalScale

namespace KernelEsmeralda

noncomputable section

def zetaNaturalCompressionTail
    (P : Zeta23.Params) (T : ℝ)
    (rho : Zeta23.zetaZeroConfig.carrier) : ℝ :=
  2 * (imaginaryEnergyDecayEnvelope P T
    (Zeta23.gammaOf (rho : Complex))) ^ 2 *
      ((((Zeta23.D0 T) + P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) + P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T)) +
  2 * (imaginaryEnergyDecayEnvelope P T
    (Zeta23.gammaOf (rho : Complex))) ^ 2 *
      ((((Zeta23.D0 T) - P.hgrid T) ^ 4)⁻¹ +
        (((Zeta23.D0 T) - P.hgrid T) ^ 3)⁻¹ /
          (3 * P.hgrid T))

end
end KernelEsmeralda
