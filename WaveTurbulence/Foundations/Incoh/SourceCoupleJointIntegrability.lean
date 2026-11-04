/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Incoh.SourceCoupleExtension
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-!
# Spectral Fubini for the actual source couple family

This conditional typing helper uses the physical root L¹ bound. The
analytic core supplies that bound independently of every Fourier shift.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual source mixture is jointly integrable whenever its root marginals have a finite
uniform physical L¹ bound. This is a Fubini helper, not the source decay theorem. -/
theorem MomentumTreeData.integrable_sourceCoupleMixture_of_uniformRootL1 {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N) (k : Mom d) :
    Integrable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      P.sourceSpectralAmplitude ζ f c z k v.2 *
        R.coupleExtension rootCutoff L γ δ (P.spectralLinks Q z v.2) I v.1) := by
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl contDiff_rootCutoff hasCompactSupport_rootCutoff
  let C := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hC : C < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  apply integrable_amplitude_mul_family_of_uniformL1 volume
    (P.sourceSpectralAmplitude ζ f c z k)
    (P.continuous_sourceSpectralAmplitude ζ f c z hK hB h k).stronglyMeasurable
    (P.integrable_sourceSpectralAmplitude ζ f c z hK hB h k)
    (fun t ξ => R.coupleExtension rootCutoff L γ δ (P.spectralLinks Q z ξ) I t)
    (P.stronglyMeasurable_spectral_coupleExtension R hL γ δ Q z hI contDiff_rootCutoff.continuous.measurable)
    (fun ξ => R.integrable_coupleExtension contDiff_rootCutoff hc hL γ δ (P.spectralLinks Q z ξ) hI hbox)
    (ENNReal.mul_lt_top hC hN)
  intro ξ
  exact (R.eLpNorm_coupleExtension_one_le contDiff_rootCutoff hc hL γ δ
    (P.spectralLinks Q z ξ) hI hbox).trans (mul_le_mul' le_rfl (hb ξ))

end WaveTurbulence.Incoh
