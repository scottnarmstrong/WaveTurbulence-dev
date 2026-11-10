/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellCutoffCoupleFamily
public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.SpectralSpatialMixture

/-! Ported by source from C2-B-TOP `Cut2BReg.AllCellMaskedCoupleDecay` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Full actual spatial mixed-norm decay after source-cell recombination

TARGET Proposition 5.1, couple case. Every spatial derivative and root
weight is taken on the actual masked source extension. Input Fourier
moments, summability, differentiation and Fubini are proved internally.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual all-cell source extension with its fixed smooth root masks. -/
@[expose] def MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (τ t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ Q I S (t + τ) u ∂sourceCellMeasure S

end WaveTurbulence.Flower.IncTop