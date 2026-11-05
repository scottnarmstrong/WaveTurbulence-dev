/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpectralCoefficient

/-! # The common spatial sample measure for all localized couple cells

Leaf and link centers use counting measure, and the independent leaf
frequencies use ordinary product Lebesgue measure. Link centers are
restricted to the actual finite geometric cover.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp Links
open scoped ENNReal

/-- The sample contains both localization arrays and the independent leaf frequencies. -/
abbrev LeafSpatialSample (d n m : ℕ) :=
  ((Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ)) × (Fin m → Fin d → ℝ)

/-- The common measure is chosen before root momenta and temporal frequencies. -/
def leafSpatialMeasure (d n m : ℕ) : Measure (LeafSpatialSample d n m) :=
  (Measure.count : Measure ((Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ))).prod volume

/-- The common density paying the first leaf frequency moment and the finite cell count. -/
def leafSpatialEnvelope {d n m : ℕ} (F : Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (p : LeafSpatialSample d n m) : ℝ≥0∞ :=
  if p.1.2 ∈ S p.1.1 then
    ENNReal.ofReal (1+∑ a, ‖toLp 2 (p.2 a)‖)*‖leafSpectrumCoefficient F p.1.1 p.2‖ₑ
  else 0

/-- All center choices are countable, so no regularity of the finite-cover choice is needed. -/
theorem measurable_leafSpatialEnvelope {d n m K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    Measurable (leafSpatialEnvelope F S) := by
  classical
  apply measurable_from_prod_countable_right
  intro c
  dsimp only [leafSpatialEnvelope]
  by_cases hh : c.2 ∈ S c.1
  · simp only [hh,ite_true]
    have hm : Measurable (fun α : Fin m → Fin d → ℝ => ‖leafSpectrumCoefficient F c.1 α‖ₑ) :=
      ((stronglyMeasurable_leafSpectrumCoefficient hK hB hF).comp_measurable
        (measurable_const.prodMk measurable_id)).enorm
    exact (by fun_prop : Measurable (fun α : Fin m → Fin d → ℝ =>
      ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖))).mul hm
  · simp only [hh,ite_false]
    exact measurable_const

/-- Exact integral of the common envelope. -/
theorem lintegral_leafSpatialEnvelope {d n m : ℕ} (F : Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hm : Measurable (leafSpatialEnvelope F S)) :
    (∫⁻ p, leafSpatialEnvelope F S p ∂leafSpatialMeasure d n m) =
      ∑' c : Fin m → Fin d → ℤ, (S c).card *
        ∫⁻ α : Fin m → Fin d → ℝ, ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*
          ‖leafSpectrumCoefficient F c α‖ₑ := by
  classical
  rw [leafSpatialMeasure,lintegral_prod _ hm.aemeasurable,lintegral_count,ENNReal.tsum_prod']
  apply tsum_congr
  intro c
  have hz (z : (Fin n × Fin 2) → Fin d → ℤ) (hz : z ∉ S c) :
      (∫⁻ α : Fin m → Fin d → ℝ, leafSpatialEnvelope F S ((c,z),α)) = 0 := by
    simp only [leafSpatialEnvelope,hz,ite_false,lintegral_zero]
  rw [tsum_eq_sum hz]
  calc
    _ = ∑ _z ∈ S c, ∫⁻ α : Fin m → Fin d → ℝ,
        ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*‖leafSpectrumCoefficient F c α‖ₑ := by
      apply Finset.sum_congr rfl
      intro z hz'
      simp only [leafSpatialEnvelope,hz',ite_true]
    _ = _ := by simp

/-- The geometric cell count and all leaf centers are paid by one common
first-moment mass, uniformly in root momentum and temporal frequency. -/
theorem lintegral_leafSpatialEnvelope_le {d n m K M : ℕ} {F : Mom d → ℂ} {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ C^n) :
    (∫⁻ p, leafSpatialEnvelope F S p ∂leafSpatialMeasure d n m) ≤
      ENNReal.ofReal (C^n)*ENNReal.ofReal (leafFirstMomentConstant d M*B)^m := by
  rw [lintegral_leafSpatialEnvelope F S
    (measurable_leafSpatialEnvelope (by omega : d+1 ≤ K) hB hF S)]
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C^n)*
      ∫⁻ α : Fin m → Fin d → ℝ, ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*
        ‖leafSpectrumCoefficient F c α‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcard c)
    _ = ENNReal.ofReal (C^n)*(∑' c : Fin m → Fin d → ℤ,
      ∫⁻ α : Fin m → Fin d → ℝ, ENNReal.ofReal (1+∑ a, ‖toLp 2 (α a)‖)*
        ‖leafSpectrumCoefficient F c α‖ₑ) := ENNReal.tsum_mul_left
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      simp only [enorm_leafSpectrumCoefficient]
      exact tsum_leafFrequency_firstMoment_le hK hM hB hF

end WaveTurbulence.RegAsymp
