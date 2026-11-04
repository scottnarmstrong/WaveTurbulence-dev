/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellSourceFamily

/-!
# Absolute spectral integrability across every actual localization cell

The previously computed actual localization mass supplies the full Fubini
integrability bound, uniformly in root momentum and global garden phase.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Source spatial norms and finite cell cardinality give actual full amplitude integrability. -/
theorem MomentumTreeData.integrable_allCellSpectralAmplitude {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    {B : ℝ} (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Integrable (P.allCellSpectralAmplitude ζ f S k) (sourceCellMeasure S) := by
  refine ⟨(P.stronglyMeasurable_allCellSpectralAmplitude ζ f S hK hB h k).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    _ = ∫⁻ u, ‖localizedSpectralReference (n := n) f u.1.1 u.2‖ₑ ∂sourceCellMeasure S := by
      apply lintegral_congr
      intro u
      exact P.enorm_sourceSpectralAmplitude ζ f u.1.1 u.1.2.val k u.2
    _ ≤ ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) :=
      lintegral_sourceCellMeasure_reference_le S hS f hK hM hB h
    _ < ⊤ := by finiteness

/-- The actual full spectral reference envelope is measurable. -/
theorem measurable_allCellSpectralReference {d n m K M : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Measurable (fun u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ) =>
      ‖localizedSpectralReference (n := n) f u.1.1 u.2‖ₑ) :=
  measurable_from_prod_countable_right (fun u =>
    (continuous_localizedSpectralReference f u.1 hK hB h).measurable.enorm)

end WaveTurbulence.Incoh
