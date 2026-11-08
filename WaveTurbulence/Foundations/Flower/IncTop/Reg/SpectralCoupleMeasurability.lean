/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralRootMeasurability
public import WaveTurbulence.Foundations.Incoh.ParametricDoubleIntegral
public import WaveTurbulence.Foundations.Incoh.CoupleExtension

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralCoupleMeasurability` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Measurability of the actual spectral couple extension

The source time indicator is arbitrary measurable data. The root marginal,
local-clock translation and literal cutoff integration all retain joint
strong measurability in the external clocks and all Fourier variables.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual local spectral root densities form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_localLinkDensitySpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      R.localLinkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1) := by
  have h := (MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatial (P := P)) R hL γ δ Q z hI
  exact h.comp_measurable
    (g := fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (v.1 + R.baseRootTimes Q, v.2)) (by fun_prop)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The literal spectral couple extensions satisfy the joint measurability needed by Tonelli. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      R.coupleExtension χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1) := by
  have h := stronglyMeasurable_cutoffDoubleIntegral_family hχ
    (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      R.localLinkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1)
    ((MomentumTreeData.stronglyMeasurable_spectral_localLinkDensitySpatial (P := P)) R hL γ δ Q z hI)
  exact h.comp_measurable
    (g := fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (v.1 - R.baseRootTimes Q, v.2)) (by fun_prop)

end WaveTurbulence.Flower.IncTop