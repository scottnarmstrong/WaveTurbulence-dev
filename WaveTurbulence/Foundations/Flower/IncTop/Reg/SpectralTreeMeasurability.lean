/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralRootMeasurability
public import WaveTurbulence.Foundations.Incoh.ParametricTriangleIntegral
public import WaveTurbulence.Foundations.Incoh.ParameterTreeExtension

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralTreeMeasurability` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Measurability of the actual spectral tree extension

The source root marginal and both orientations of causal cutoff integration
retain joint strong measurability in clocks and Fourier variables.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual causal spectral tree extensions form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_treeExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I) v.1) :=
  stronglyMeasurable_cutoffTriangleIntegral_family hχ
    (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1)
    ((MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatial (P := P)) R hL γ δ Q z hI)

end WaveTurbulence.Flower.IncTop