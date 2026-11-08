/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAmplitudeIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceCellMassBound` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Total mass of the actual countable source localization measure

The finite link-cell cardinal bound and summable actual leaf Fourier
norms give a finite coefficient before applying any temporal estimate.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Source spatial norms prove continuity of the actual common reference density. -/
theorem continuous_localizedSpectralReferenceSpatial {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    Continuous (localizedSpectralReference (n := n) f c) := by
  unfold localizedSpectralReference
  apply continuous_finsetProd
  intro i _
  exact (Fourier.timeFourier_continuous (Fourier.integrable_of_timeFourierNorm_lt_top
    (timeFourierNorm_localizedCellProfiles_lt_top f c (fun _ => 0) hK hB h i))).comp (continuous_apply i)

/-- Exact input-generated envelope over all selected source cells has a uniform exponential mass. -/
theorem lintegral_sourceCellMeasure_reference_leSpatial {d n m K M : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (f : Fin m → Mom d → ℂ) {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∫⁻ u, ‖localizedSpectralReference (n := n) f u.1.1 u.2‖ₑ ∂sourceCellMeasure S) ≤
      ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  rw [lintegral_sourceCellMeasure S _ (fun c => (continuous_localizedSpectralReferenceSpatial f c hK hB h).measurable.enorm)]
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C ^ n) *
        ∫⁻ ξ, ‖localizedSpectralReference (n := n) f c ξ‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hS c)
    _ = ENNReal.ofReal (C ^ n) * ∑' c : Fin m → Fin d → ℤ,
        ∫⁻ ξ, ‖localizedSpectralReference (n := n) f c ξ‖ₑ := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (tsum_lintegral_enorm_localizedSpectralReference_le f hK hM hB h)

end WaveTurbulence.Flower.IncTop