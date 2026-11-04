/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralMomentProfiles

/-! # Continuity of actual higher-moment spectral envelopes -/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Each actual Fourier moment profile is continuous in its literal frequency variable. -/
theorem continuous_spectralMomentProfile {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (i : LocalizedCellIndex n m) : Continuous (spectralMomentProfile J f c i) := by
  cases i with
  | inl a =>
      have hc := Fourier.timeFourier_continuous
        (Fourier.integrable_of_timeFourierNorm_lt_top
          ((timeFourierNorm_leafCell_le hK hB (h a) (c a)).trans_lt ENNReal.ofReal_lt_top))
      have ht : Continuous (fun ξ : Fin d → ℝ => (toLp 2 ξ : Mom d)) :=
        PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)
      exact (Complex.continuous_ofReal.comp ((continuous_const.add ht.norm).pow J)).mul hc
  | inr p =>
      exact Fourier.timeFourier_continuous
        (Fourier.integrable_of_timeFourierNorm_lt_top (timeFourierNorm_halfLinkCell_lt_top 0 0))

/-- The literal higher-moment reference density is continuous jointly in all Fourier variables. -/
theorem continuous_localizedSpectralMomentReference {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Continuous (localizedSpectralMomentReference (n := n) J f c) := by
  apply continuous_finsetProd
  intro i _
  exact (continuous_spectralMomentProfile J f c hK hB h i).comp (continuous_apply i)

end WaveTurbulence.Incoh
