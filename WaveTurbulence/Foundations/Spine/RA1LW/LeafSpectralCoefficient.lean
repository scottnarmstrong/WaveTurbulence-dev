/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafModulationMoment

/-! # Jointly measurable actual leaf Fourier coefficients -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp Links
open scoped ENNReal

/-- The actual leaf Fourier coefficient, with independent source frequencies. -/
def leafSpectrumCoefficient {d m : ℕ} (F : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) : ℂ :=
  ∏ a, Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 y)) (α a)

/-- The first source moment implies continuity of each ordinary leaf transform. -/
theorem continuous_timeFourier_leafCell {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) :
    Continuous (Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F c (toLp 2 y))) := by
  have hb := timeFourierNorm_leafCell_le hK hB hF c
  exact Fourier.timeFourier_continuous
    (Fourier.integrable_of_timeFourierNorm_lt_top (hb.trans_lt ENNReal.ofReal_lt_top))

/-- All countably many localization centers may be included in the auxiliary measure. -/
theorem stronglyMeasurable_leafSpectrumCoefficient {d m K M : ℕ} {F : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) :
    StronglyMeasurable (fun p : (Fin m → Fin d → ℤ) × (Fin m → Fin d → ℝ) =>
      leafSpectrumCoefficient F p.1 p.2) := by
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_right
  intro c
  unfold leafSpectrumCoefficient
  apply Finset.measurable_fun_prod
  intro a _
  exact (continuous_timeFourier_leafCell hK hB (hF a) (c a)).measurable.comp (measurable_pi_apply a)

/-- The common first-moment norm has the literal coefficient norm. -/
theorem enorm_leafSpectrumCoefficient {d m : ℕ} (F : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) :
    ‖leafSpectrumCoefficient F c α‖ₑ =
      ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 y)) (α a)‖ₑ := by
  simp only [leafSpectrumCoefficient,ApproxNT.enorm_finset_prod]

/-- The transpose of the actual integer node map is continuous in all leaf frequencies. -/
theorem continuous_sourceFrequencyPullback {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (j : LinkCoord Q) :
    Continuous (fun α : Fin (2*Q.links.length+1) → Mom d => sourceFrequencyPullback hQ hG α j) := by
  unfold sourceFrequencyPullback
  fun_prop

end WaveTurbulence.RA1Leafwise
