/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.UnrestrictedCellMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellMassBound
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralTreeMeasurability
public import WaveTurbulence.Foundations.Incoh.CutoffTriangleL1
public import WaveTurbulence.Foundations.Incoh.GeneralTriangleNegativeNorm
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.MovingTreeFamily` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Actual causal kernel family for moving tree localization

The fixed measure counts every integer cell. The kernel is the actual
spectral causal extension; the source amplitude retains its moving mask.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual causal spectral link kernel on the fixed unrestricted cell measure. -/
@[expose] def MomentumTreeData.unrestrictedTreeKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) I) t

end WaveTurbulence.Flower.IncTop