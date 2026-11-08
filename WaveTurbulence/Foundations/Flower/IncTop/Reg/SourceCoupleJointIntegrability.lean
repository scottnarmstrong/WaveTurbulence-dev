/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCoupleExtension
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceCoupleJointIntegrability` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Spectral Fubini for the actual source couple family

This conditional typing helper uses the physical root L¹ bound. The
analytic core supplies that bound independently of every Fourier shift.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual source mixture is jointly integrable whenever its root marginals have a finite
uniform physical L¹ bound. This is a Fubini helper, not the source decay theorem. -/
theorem MomentumTreeData.integrable_sourceCoupleMixture_of_uniformRootL1Spatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N) (k : Mom d) :
    Integrable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k v.2 *
        R.coupleExtension rootCutoff L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) I v.1) := by
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl contDiff_rootCutoff hasCompactSupport_rootCutoff
  let C := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hC : C < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  apply integrable_amplitude_mul_family_of_uniformL1 volume
    ((MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k)
    ((MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z hK hB h k).stronglyMeasurable
    ((MomentumTreeData.integrable_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z hK hB h k)
    (fun t ξ => R.coupleExtension rootCutoff L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I t)
    ((MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatial (P := P)) R hL γ δ Q z hI contDiff_rootCutoff.continuous.measurable)
    (fun ξ => R.integrable_coupleExtension contDiff_rootCutoff hc hL γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) hI hbox)
    (ENNReal.mul_lt_top hC hN)
  intro ξ
  exact (R.eLpNorm_coupleExtension_one_le contDiff_rootCutoff hc hL γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) hI hbox).trans (mul_le_mul' le_rfl (hb ξ))

end WaveTurbulence.Flower.IncTop