/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.GrowthProfiles

/-! # Explicit scalar majorants for the high-γ counting proof -/

public section
namespace WaveTurbulence.CountLemmas

@[expose] noncomputable def pairStripFactor (d : ℕ) (c δ γ L : ℝ) : ℝ :=
  1+2*(d : ℝ)*c*(δ⁻¹*L^(-2*γ))*L^2

@[expose] noncomputable def pairRadialFactor (d : ℕ) (c δ γ L : ℝ) : ℝ :=
  (3^(d-1)*L^(d-1))^2*pairStripFactor d c δ γ L

/-- The actual terminal-box and two geometric radial contributions. -/
@[expose] noncomputable def pairSmallMajorant (d : ℕ) (c δ γ ε L : ℝ) : ℝ :=
  15^d*L^d+2*pairRadialFactor d c δ γ L*(L^(-ε))^(d-1)+
    2*(pairRadialFactor d c δ γ L*(4*(d : ℝ)*(δ⁻¹*L^(-2*γ))*L))*(L^(-ε))^(d-2)

@[expose] noncomputable def densePairConstant (d : ℕ) : ℝ :=
  2*((5 : ℝ)^d+(d : ℝ)*129600*((3 : ℝ)^(d-2))^3)

/-- The actual sparse term and the estcross exceptional-density term. -/
@[expose] noncomputable def pairDenseMajorant (d : ℕ) (c δ γ ε L : ℝ) : ℝ :=
  (2*L+1)^(d-1)*pairStripFactor d c δ γ L*(L^(d-1)/L^ε)+
    (densePairConstant d*L^(d-2)*((δ⁻¹*L^(-2*γ))*L^2)^2*(L^ε)^2*(1+Real.log L)^2)*
      ((2*L+1)^(d-1)*(2*(d : ℝ)*(δ⁻¹*L^(-2*γ))*L/L^(-ε)+1))

end WaveTurbulence.CountLemmas
