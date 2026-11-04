/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralMomentProfiles

/-! # Integrable higher-moment spectral envelopes with summable source-center decay -/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual higher-moment mass factors over individual Fourier profiles. -/
theorem lintegral_enorm_localizedSpectralMomentReference {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ‖localizedSpectralMomentReference J f c ξ‖ₑ) =
        ∏ i : LocalizedCellIndex n m, ∫⁻ ξ : Fin d → ℝ, ‖spectralMomentProfile J f c i ξ‖ₑ := by
  have hi := integrable_localizedSpectralMomentReference (n := n) J f c hK hB h
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [localizedSpectralMomentReference, norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun i ξ => ‖spectralMomentProfile J f c i ξ‖)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))]
  exact Finset.prod_congr rfl (fun i _ => ofReal_integral_norm_eq_lintegral_enorm
    (integrable_spectralMomentProfile J f c hK hB h i))

/-- One actual leaf moment carries the full source center decay. -/
theorem lintegral_enorm_spectralMomentProfile_leaf_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (a : Fin m) :
    (∫⁻ ξ : Fin d → ℝ, ‖spectralMomentProfile (n := n) J f c (.inl a) ξ‖ₑ) ≤
      ENNReal.ofReal (leafCellFourierMomentConstant d J M * B /
        Fourier.momentumBracket (NTSP.intVec (c a)) ^ M) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_spectralMomentProfile J f c hK hB h (.inl a))]
  have habs (ξ : Fin d → ℝ) : |(1 + ‖toLp 2 ξ‖) ^ J| = (1 + ‖toLp 2 ξ‖) ^ J := abs_of_nonneg (by positivity)
  simp only [spectralMomentProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
  exact ENNReal.ofReal_le_ofReal
    (integrable_coordinate_fourierMoment_leafCell_and_integral_le hK hB (h a) (c a)).2

/-- The link profiles incur no spatial derivative moments. -/
theorem lintegral_enorm_spectralMomentProfile_link_le {d n m : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) (p : Fin n × Fin 2) :
    (∫⁻ ξ : Fin d → ℝ, ‖spectralMomentProfile J f c (.inr p) ξ‖ₑ) ≤
      ENNReal.ofReal (halfCellFourierConstant d) := by
  have hi := Fourier.integrable_of_timeFourierNorm_lt_top (timeFourierNorm_halfLinkCell_lt_top 0 (0 : Fin d → ℤ))
  have he := Fourier.timeFourierNorm_eq_lintegral (θ := (0 : ℝ)) hi
  simp only [Fourier.timeWeight, Real.rpow_zero, ENNReal.ofReal_one, one_mul] at he
  change (∫⁻ ξ : Fin d → ℝ, ‖Fourier.timeFourier
    (fun x => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x)) ξ‖ₑ) ≤ _
  rw [← he]
  exact timeFourierNorm_halfLinkCell_le d 0

/-- Explicit actual spectral-moment mass bound for a single leaf-center array. -/
theorem lintegral_enorm_localizedSpectralMomentReference_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ) ≤
      (∏ a : Fin m, ENNReal.ofReal (leafCellFourierMomentConstant d J M * B /
        Fourier.momentumBracket (NTSP.intVec (c a)) ^ M)) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  rw [lintegral_enorm_localizedSpectralMomentReference J f c hK hB h, Fintype.prod_sum_type]
  apply mul_le_mul'
    (Finset.prod_le_prod (fun a _ => lintegral_enorm_spectralMomentProfile_leaf_le J f c hK hB h a))
  calc
    _ ≤ ∏ _p : Fin n × Fin 2, ENNReal.ofReal (halfCellFourierConstant d) :=
      Finset.prod_le_prod (fun p _ => lintegral_enorm_spectralMomentProfile_link_le J f c p)
    _ = _ := by simp [Nat.mul_comm]

end WaveTurbulence.Incoh
