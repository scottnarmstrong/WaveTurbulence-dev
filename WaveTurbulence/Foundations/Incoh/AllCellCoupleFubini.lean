/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellAmplitudeL1
public import WaveTurbulence.Foundations.Incoh.SourceCoupleJointIntegrability

/-!
# Fubini on all actual couple localization cells

The countable localization coefficient is integrable. Uniform physical
root-marginal control therefore gives joint time/localization integrability.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional Fubini helper over all actual cells, using their independently bounded mass. -/
theorem MomentumTreeData.integrable_allCellCoupleMixture_of_uniformRootL1 {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N) (k : Mom d) :
    Integrable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      P.allCellSpectralAmplitude ζ f S k v.2 * P.allCellCoupleKernel R L γ δ Q I S v.1 v.2)
      (volume.prod (sourceCellMeasure S)) := by
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl contDiff_rootCutoff hasCompactSupport_rootCutoff
  let A := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hA : A < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  apply integrable_amplitude_mul_family_of_uniformL1 (sourceCellMeasure S)
    (P.allCellSpectralAmplitude ζ f S k)
    (P.stronglyMeasurable_allCellSpectralAmplitude ζ f S hK hB h k)
    (P.integrable_allCellSpectralAmplitude ζ f S hS hK hM hB h k)
    (P.allCellCoupleKernel R L γ δ Q I S)
    (P.stronglyMeasurable_allCellCoupleKernel R hL γ δ Q I hI S)
    (fun u => R.integrable_coupleExtension contDiff_rootCutoff hc hL γ δ
      (P.spectralLinks Q u.1.2.val u.2) hI hbox) (ENNReal.mul_lt_top hA hN)
  intro u
  exact (R.eLpNorm_coupleExtension_one_le contDiff_rootCutoff hc hL γ δ
    (P.spectralLinks Q u.1.2.val u.2) hI hbox).trans (mul_le_mul' le_rfl (hb _ _))

end WaveTurbulence.Incoh
