/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.UnrestrictedCellMeasure
public import WaveTurbulence.Foundations.Incoh.SourceCellMassBound
public import WaveTurbulence.Foundations.Incoh.SpectralTreeMeasurability
public import WaveTurbulence.Foundations.Incoh.CutoffTriangleL1
public import WaveTurbulence.Foundations.Incoh.GeneralTriangleNegativeNorm
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-!
# Actual causal kernel family for moving tree localization

The fixed measure counts every integer cell. The kernel is the actual
spectral causal extension; the source amplitude retains its moving mask.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Actual causal spectral link kernel on the fixed unrestricted cell measure. -/
@[expose] def MomentumTreeData.unrestrictedTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q u.1.2 u.2) I) t

end WaveTurbulence.Incoh
