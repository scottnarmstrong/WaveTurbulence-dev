/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpatialMeasure
public import WaveTurbulence.Foundations.RegAsymp.LeafWeightedMomentMass

/-! # The actual root-weighted higher leaf moment envelope -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal

/-- Center weights pay spatial decay; individual leaf moments pay derivatives and NT modulation. -/
def leafHigherMomentWeight {d m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ a, Fourier.momentumBracket (NTSP.intVec (c a))^W)*
    ENNReal.ofReal (∏ a, (1+‖toLp 2 (α a)‖)^N)*‖leafSpectrumCoefficient F c α‖ₑ

/-- The actual finite link cover is retained in the higher-moment sample envelope. -/
def leafSpatialHigherEnvelope {d n m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (p : LeafSpatialSample d n m) : ℝ≥0∞ :=
  if p.1.2 ∈ S p.1.1 then leafHigherMomentWeight N W F p.1.1 p.2 else 0

/-- The actual moment envelope is measurable without regularity of the countable cover choice. -/
theorem measurable_leafSpatialHigherEnvelope {d n m K M : ℕ} (N W : ℕ)
    {F : Fin m → Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    Measurable (leafSpatialHigherEnvelope N W F S) := by
  classical
  apply measurable_from_prod_countable_right
  intro c
  by_cases hc : c.2 ∈ S c.1
  · simp only [leafSpatialHigherEnvelope,hc,ite_true,leafHigherMomentWeight]
    have hm : Measurable (fun α : Fin m → Fin d → ℝ => ‖leafSpectrumCoefficient F c.1 α‖ₑ) :=
      ((stronglyMeasurable_leafSpectrumCoefficient hK hB hF).comp_measurable
        (measurable_const.prodMk measurable_id)).enorm
    have hw : Measurable (fun α : Fin m → Fin d → ℝ =>
        ENNReal.ofReal (∏ a, (1+‖toLp 2 (α a)‖)^N)) := by fun_prop
    exact (measurable_const.mul hw).mul hm
  · simp only [leafSpatialHigherEnvelope,hc,ite_false]
    exact measurable_const

/-- The actual countable-center integral is its literal finite-cover cardinality sum. -/
theorem lintegral_leafSpatialHigherEnvelope {d n m : ℕ} (N W : ℕ) (F : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hm : Measurable (leafSpatialHigherEnvelope N W F S)) :
    (∫⁻ p, leafSpatialHigherEnvelope N W F S p ∂leafSpatialMeasure d n m) =
      ∑' c : Fin m → Fin d → ℤ, (S c).card * ∫⁻ α, leafHigherMomentWeight N W F c α := by
  classical
  rw [leafSpatialMeasure,lintegral_prod _ hm.aemeasurable,lintegral_count,ENNReal.tsum_prod']
  apply tsum_congr
  intro c
  have hz (z : (Fin n × Fin 2) → Fin d → ℤ) (hz : z ∉ S c) :
      (∫⁻ α : Fin m → Fin d → ℝ, leafSpatialHigherEnvelope N W F S ((c,z),α)) = 0 := by
    simp only [leafSpatialHigherEnvelope,hz,ite_false,lintegral_zero]
  rw [tsum_eq_sum hz]
  calc
    _ = ∑ _z ∈ S c, ∫⁻ α : Fin m → Fin d → ℝ, leafHigherMomentWeight N W F c α := by
      apply Finset.sum_congr rfl
      intro z hz'
      simp only [leafSpatialHigherEnvelope,hz',ite_true]
    _ = _ := by simp

/-- All centers and all actual Fourier moments have a geometric mass,
with only the remaining center exponent M-W used for summability. -/
theorem lintegral_leafSpatialHigherEnvelope_le {d n m K M : ℕ} (N W : ℕ)
    {F : Fin m → Mom d → ℂ} {B C : ℝ} (hK : d+1+N ≤ K) (hM : W+2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ C^n) :
    (∫⁻ p, leafSpatialHigherEnvelope N W F S p ∂leafSpatialMeasure d n m) ≤
      ENNReal.ofReal (C^n)*ENNReal.ofReal (leafWeightedMomentLocalizationConstant d N M W*B)^m := by
  rw [lintegral_leafSpatialHigherEnvelope N W F S
    (measurable_leafSpatialHigherEnvelope N W (by omega) hB hF S)]
  have hprod (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) :
      ENNReal.ofReal (∏ a, (1+‖toLp 2 (α a)‖)^N)*‖leafSpectrumCoefficient F c α‖ₑ =
      ∏ a, ‖((((1+‖toLp 2 (α a)‖)^N:ℝ):ℂ)*
        Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 y)) (α a))‖ₑ := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),enorm_leafSpectrumCoefficient,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    have hs : ‖((((1+‖toLp 2 (α a)‖)^N:ℝ):ℂ))‖ₑ = ENNReal.ofReal ((1+‖toLp 2 (α a)‖)^N) := by
      rw [← ofReal_norm,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [enorm_mul,hs]
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C^n)*∫⁻ α, leafHigherMomentWeight N W F c α := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcard c)
    _ = ENNReal.ofReal (C^n)*(∑' c : Fin m → Fin d → ℤ, ∫⁻ α, leafHigherMomentWeight N W F c α) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      simp only [leafHigherMomentWeight,mul_assoc]
      simp_rw [hprod]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact tsum_weighted_leafMoment_product_le N F hK hM hB hF

end WaveTurbulence.RA1Leafwise
