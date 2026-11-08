/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralLinkContinuity
public import WaveTurbulence.Foundations.Incoh.LocalRootDensity

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralRootMeasurability` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Joint measurability of actual spectral root marginals

The time-domain indicator is literal and merely measurable. Integrating
out the complementary structural coordinates preserves strong measurability.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual normalized spectral link integrand is jointly measurable. -/
theorem MomentumTreeData.measurable_spectral_normalizedLinkIntegrandSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    Measurable (fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      normalizedLinkIntegrand L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1) := by
  have hp : Continuous (fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      ∏ i, linkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i) (v.1 i)) := by
    apply continuous_finsetProd
    intro i _
    exact ((MomentumTreeData.continuous_spectral_linkTimeFactorSpatial (P := P)) hL γ δ Q z i).comp
      (f := fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) => (v.1 i, v.2))
      (by fun_prop)
  convert (hp.measurable.indicator (hI.preimage measurable_fst)).const_mul
    (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) using 1
  funext v
  by_cases hv : v.1 ∈ I <;> simp [normalizedLinkIntegrand, hv]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual spectral root marginals form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatial {d n m w r : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n r) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    StronglyMeasurable (fun v : (Fin r → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1) := by
  have he : Measurable (fun v : ((Fin r → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) ×
      (Fin R.restCount → ℝ) => R.equiv.symm (v.1.1, v.2)) :=
    R.equiv.symm.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hn := ((MomentumTreeData.measurable_spectral_normalizedLinkIntegrandSpatial (P := P)) hL γ δ Q z hI).stronglyMeasurable
  exact (hn.comp_measurable (he.prodMk (measurable_snd.comp measurable_fst))).integral_prod_right'

end WaveTurbulence.Flower.IncTop