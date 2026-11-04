/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.UnrestrictedCellMeasure
public import WaveTurbulence.Foundations.Incoh.SourceCellMassBound

/-!
# Actual amplitudes for root-dependent finite localization supports

A moving finite cell selection is an indicator in the literal source
amplitude. Its mass is bounded uniformly in the root momentum.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual source amplitude, retaining the moving finite selection as an indicator. -/
@[expose] def MomentumTreeData.movingCellAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  if u.1.2 ∈ S k u.1.1 then P.sourceSpectralAmplitude ζ f u.1.1 u.1.2 k u.2 else 0

/-- The actual moving amplitude has an exact input-generated pointwise envelope. -/
theorem MomentumTreeData.enorm_movingCellAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :
    ‖P.movingCellAmplitude ζ f S k u‖ₑ =
      if u.1.2 ∈ S k u.1.1 then ‖localizedSpectralReference (n := n) f u.1.1 u.2‖ₑ else 0 := by
  unfold movingCellAmplitude
  split_ifs
  · exact P.enorm_sourceSpectralAmplitude ζ f u.1.1 u.1.2 k u.2
  · exact enorm_zero

/-- Every fixed root gives a strongly measurable actual moving amplitude. -/
theorem MomentumTreeData.stronglyMeasurable_movingCellAmplitude {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    StronglyMeasurable (P.movingCellAmplitude ζ f S k) := by
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_right
  intro u
  unfold movingCellAmplitude
  dsimp only
  split_ifs
  · exact (P.continuous_sourceSpectralAmplitude ζ f u.1 u.2 hK hB h k).measurable
  · exact measurable_const

/-- The full actual spectral amplitude mass is uniform even when the selected cells move. -/
theorem MomentumTreeData.lintegral_enorm_movingCellAmplitude_le {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ k c, ((S k c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (∫⁻ u, ‖P.movingCellAmplitude ζ f S k u‖ₑ ∂unrestrictedCellMeasure d n m) ≤
      ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  rw [lintegral_congr (fun u => P.enorm_movingCellAmplitude ζ f S k u)]
  rw [lintegral_unrestrictedCellMeasure_indicator (S k)
    (fun c ξ => ‖localizedSpectralReference (n := n) f c ξ‖ₑ)
    (fun c => (continuous_localizedSpectralReference f c hK hB h).measurable.enorm)]
  rw [← lintegral_sourceCellMeasure (S k) (fun c ξ => ‖localizedSpectralReference (n := n) f c ξ‖ₑ)
    (fun c => (continuous_localizedSpectralReference f c hK hB h).measurable.enorm)]
  exact lintegral_sourceCellMeasure_reference_le (S k) (hS k) f hK hM hB h

/-- Input spatial bounds prove absolute spectral integrability of the actual moving amplitude. -/
theorem MomentumTreeData.integrable_movingCellAmplitude {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ k c, ((S k c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Integrable (P.movingCellAmplitude ζ f S k) (unrestrictedCellMeasure d n m) := by
  refine ⟨(P.stronglyMeasurable_movingCellAmplitude ζ f S hK hB h k).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact (P.lintegral_enorm_movingCellAmplitude_le ζ f S hS hK hM hB h k).trans_lt (by finiteness)

end WaveTurbulence.Incoh
