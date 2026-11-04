/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellFourierMoment
public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMassBound

/-! # Actual individual Fourier moment profiles for the source density -/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Multiply each actual leaf Fourier profile by its required frequency moment. Link profiles
retain order zero, since the root frequency has no link-profile contribution. -/
@[expose] def spectralMomentProfile {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) : LocalizedCellIndex n m → (Fin d → ℝ) → ℂ
  | .inl a, ξ => ((1 + ‖toLp 2 ξ‖) ^ J : ℝ) *
      Fourier.timeFourier (fun x => leafCell (f a) (c a) (toLp 2 x)) ξ
  | .inr _, ξ => Fourier.timeFourier (fun x => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x)) ξ

/-- Literal higher-moment reference density. -/
@[expose] def localizedSpectralMomentReference {d n m : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  ∏ i, spectralMomentProfile J f c i (ξ i)

/-- The moment profile norm is exactly the root-frequency product envelope. -/
theorem norm_localizedSpectralMomentReference {d n m : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ‖localizedSpectralMomentReference J f c ξ‖ =
      (∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ J) *
        ‖localizedSpectralReference (n := n) f c ξ‖ := by
  have habs (ξ : Fin d → ℝ) : |(1 + ‖toLp 2 ξ‖) ^ J| = (1 + ‖toLp 2 ξ‖) ^ J := abs_of_nonneg (by positivity)
  simp only [localizedSpectralMomentReference, localizedSpectralReference, norm_prod,
    Fintype.prod_sum_type, spectralMomentProfile, localizedCellProfiles, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, habs]
  rw [Finset.prod_mul_distrib]
  ring

/-- Every actual individual Fourier moment profile is integrable. -/
theorem integrable_spectralMomentProfile {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (i : LocalizedCellIndex n m) : Integrable (spectralMomentProfile J f c i) := by
  cases i with
  | inl a =>
      have hi := (integrable_coordinate_fourierMoment_leafCell_and_integral_le hK hB (h a) (c a)).1
      have hc := Fourier.timeFourier_continuous
        (Fourier.integrable_of_timeFourierNorm_lt_top
          ((timeFourierNorm_leafCell_le (by omega) hB (h a) (c a)).trans_lt ENNReal.ofReal_lt_top))
      have hm : AEStronglyMeasurable (spectralMomentProfile (n := n) J f c (.inl a)) := by
        apply Continuous.aestronglyMeasurable
        have ht : Continuous (fun ξ : Fin d → ℝ => (toLp 2 ξ : Mom d)) :=
          PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)
        exact (Complex.continuous_ofReal.comp ((continuous_const.add ht.norm).pow J)).mul hc
      have habs (ξ : Fin d → ℝ) : |(1 + ‖toLp 2 ξ‖) ^ J| = (1 + ‖toLp 2 ξ‖) ^ J := abs_of_nonneg (by positivity)
      apply (integrable_norm_iff hm).mp
      simpa only [spectralMomentProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        habs] using hi
  | inr p =>
      exact Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ))
        (timeFourierNorm_halfLinkCell_lt_top 0 0)

/-- The whole actual higher-moment reference is integrable. -/
theorem integrable_localizedSpectralMomentReference {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Integrable (localizedSpectralMomentReference (n := n) J f c) := by
  change Integrable (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
    ∏ i, spectralMomentProfile J f c i (ξ i))
    (Measure.pi (fun _ : LocalizedCellIndex n m => (volume : Measure (Fin d → ℝ))))
  exact Integrable.fintype_prod (fun i => integrable_spectralMomentProfile J f c hK hB h i)

end WaveTurbulence.Incoh
