/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralEnvelope

/-!
# Exact mass of the common localized spectral envelope

Tonelli/Fubini separates the actual profile Fourier norms. Link profiles
contribute one fixed dimensional constant for each free link coordinate.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal mass of the common spectral envelope factors into the actual cell norms. -/
theorem lintegral_enorm_localizedSpectralReference {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      ‖localizedSpectralReference (n := n) f c ξ‖ₑ) =
      ∏ i : LocalizedCellIndex n m,
        Fourier.timeFourierNorm 0 (localizedCellProfiles f c (fun _ => 0) i) := by
  have hi := integrable_localizedSpectralReference (n := n) f c hK hB h
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [localizedSpectralReference, norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun i ξ =>
    ‖Fourier.timeFourier (localizedCellProfiles f c (fun _ => 0) i) ξ‖)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))]
  apply Finset.prod_congr rfl
  intro i _
  have hf := timeFourierNorm_localizedCellProfiles_lt_top f c (fun _ => 0) hK hB h i
  rw [ofReal_integral_norm_eq_lintegral_enorm
    (Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ)) hf),
    Fourier.timeFourierNorm_eq_lintegral (Fourier.integrable_of_timeFourierNorm_lt_top hf)]
  simp only [Fourier.timeWeight, Real.rpow_zero, ENNReal.ofReal_one, one_mul]

end WaveTurbulence.Incoh
