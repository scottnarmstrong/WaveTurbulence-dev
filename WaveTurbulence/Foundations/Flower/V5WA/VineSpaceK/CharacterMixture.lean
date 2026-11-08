/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
/-! C2-B: C2-A Fourier measures as the existing V5 character-mixture data. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.VineSpaceK
open Cut2A DegenVine
variable {E : Type*} [MeasurableSpace E] {α : Type} [MeasurableSpace α]

/-- Absorb the absolute amplitude into a finite positive measure and retain its unit phase.
The only new inputs specify the affine spatial modulation and its bounded exterior character. -/
def toCharMix {d : ℕ} (S : SumintShape) (F : SpatialMeasure E α) (hamp : Measurable F.amplitude)
    (ν : E → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ z, Measurable (fun a => phase a z))
    (hphaseNorm : ∀ a z, ‖phase a z‖ ≤ 1) : CharMix S d where
  α := α
  μ := F.μ.withDensity (fun a => ‖F.amplitude a‖ₑ)
  hμ := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact F.amplitude_integrable.hasFiniteIntegral⟩
  ζ := fun a => ν (F.frequency a)
  hζ := hν.comp F.frequency_measurable
  u := fun a z => (‖F.amplitude a‖⁻¹ • F.amplitude a) * phase a z
  hu := fun z => (hamp.norm.inv.smul hamp).mul (hphase z)
  hu1 := fun a z => by
    rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hp : ‖F.amplitude a‖⁻¹ * ‖F.amplitude a‖ ≤ 1 := by
      by_cases h : F.amplitude a = 0
      · simp [h]
      · exact (inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)).le
    exact (mul_le_mul hp (hphaseNorm a z)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The character-mixture cost is precisely C2-A's presentation mass. -/
theorem toCharMix_mass {d : ℕ} (S : SumintShape) (F : SpatialMeasure E α) (hamp : Measurable F.amplitude)
    (ν : E → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ z, Measurable (fun a => phase a z))
    (hphaseNorm : ∀ a z, ‖phase a z‖ ≤ 1) :
    (toCharMix S F hamp ν hν phase hphase hphaseNorm).mass = F.mass := by
  rw [CharMix.mass, toCharMix, Measure.real, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_norm_eq_lintegral_enorm F.amplitude_integrable,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  rfl

/-- The actual multiplier, with no discarded dependence on the internal lattice decoration. -/
theorem toCharMix_val {d : ℕ} (S : SumintShape) (F : SpatialMeasure E α) (hamp : Measurable F.amplitude)
    (ν : E → S.VIdx → Mom d) (hν : Measurable ν)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ z, Measurable (fun a => phase a z))
    (hphaseNorm : ∀ a z, ‖phase a z‖ ≤ 1) (L : ℝ) (z : Fin 4 → Mom d)
    (x : S.VIdx → Fin d → ℤ) :
    (toCharMix S F hamp ν hν phase hphase hphaseNorm).val L z x =
      ∫ a, F.amplitude a * phase a z * charOf S L (ν (F.frequency a)) x ∂F.μ := by
  rw [CharMix.val, toCharMix,
    integral_withDensity_eq_integral_toReal_smul hamp.enorm (Filter.Eventually.of_forall fun _ => enorm_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    simp only [toReal_enorm]
    rw [← smul_mul_assoc, ← smul_mul_assoc, smul_smul]
    by_cases h : F.amplitude a = 0
    · simp [h]
    · rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
end WaveTurbulence.VineSpaceK
