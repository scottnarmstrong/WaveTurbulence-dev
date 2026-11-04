/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueRemainder
public import WaveTurbulence.Foundations.Resonant.PrincipalValueSlices

/-! # Principal-value cancellation for integrable Lipschitz amplitudes

The DH21 principal-value cutoff limit needs no support radius. Integrability
controls the tails, while Lipschitz cancellation controls the origin.
-/

public section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace WaveTurbulence.Resonant

private theorem pvQuotient_eq_remainders {f : ℝ → ℝ} {u : ℝ} (hu : u ≠ 0) :
    pvQuotient f u = 2⁻¹ * (pvRemainder f u + pvRemainder f (-u)) := by
  have he : (Icc (-1 : ℝ) 1).indicator (fun _ => f 0) (-u) =
      (Icc (-1 : ℝ) 1).indicator (fun _ => f 0) u := by
    by_cases h : u ∈ Icc (-1 : ℝ) 1
    · have hn : -u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith only [h.2],by linarith only [h.1]⟩
      rw [indicator_of_mem h,indicator_of_mem hn]
    · have hn : -u ∉ Icc (-1 : ℝ) 1 := by
        intro hn
        exact h ⟨by linarith only [hn.2],by linarith only [hn.1]⟩
      rw [indicator_of_notMem h,indicator_of_notMem hn]
  rw [pvQuotient_of_ne f hu]
  simp only [pvRemainder,he,inv_neg,smul_eq_mul]
  field_simp
  ring

theorem integrable_pvQuotient_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) : Integrable (pvQuotient f) := by
  have hr := integrable_pvRemainder hf hL
  apply ((hr.add hr.comp_neg).const_mul (2⁻¹ : ℝ)).congr
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
  exact (pvQuotient_eq_remainders (by simpa only [mem_singleton_iff,mem_compl_iff] using hu)).symm

theorem integral_abs_pvQuotient_le_l1 {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) :
    (∫ u, |pvQuotient f u|) ≤ 2*K + ∫ u, |f u| := by
  have hr := integrable_pvRemainder hf hL
  have hq := integrable_pvQuotient_of_lipschitz hf hL
  have hh : (∫ u, |pvQuotient f u|) ≤
      ∫ u, (2⁻¹ : ℝ)*(|pvRemainder f u|+|pvRemainder f (-u)|) := by
    apply integral_mono_ae hq.abs ((hr.abs.add hr.comp_neg.abs).const_mul _)
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
    rw [pvQuotient_eq_remainders (by simpa only [mem_singleton_iff,mem_compl_iff] using hu),abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  have he : (∫ u, (2⁻¹ : ℝ)*(|pvRemainder f u|+|pvRemainder f (-u)|)) = ∫ u, |pvRemainder f u| := by
    rw [integral_const_mul,integral_add hr.abs hr.comp_neg.abs]
    rw [integral_neg_eq_self (fun u : ℝ => |pvRemainder f u|) volume]
    ring
  exact (hh.trans_eq he).trans (by simpa only [Real.norm_eq_abs] using integral_norm_pvRemainder_le hf hL)

namespace IsPVCutoff
variable {χ : ℝ → ℝ}

theorem pvTruncation_eq_of_integrable (hχ : IsPVCutoff χ) {f : ℝ → ℝ}
    (hf : Integrable f) (μ : ℝ) :
    pvTruncation χ μ f = ∫ u, (1-χ (μ*u))*pvQuotient f u := by
  let q : ℝ → ℝ := fun u => (1-χ (μ*u))/u
  obtain ⟨C,_,hC⟩ := hχ.exists_bound_div μ
  have hi : Integrable (fun u => q u*f u) := by
    exact (hf.mul_bdd (hχ.continuous_div μ).aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC u)).congr
        (Eventually.of_forall fun u => mul_comm _ _)
  have hni : Integrable (fun u => q u*f (-u)) := by
    exact (hf.comp_neg.mul_bdd (hχ.continuous_div μ).aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC u)).congr
        (Eventually.of_forall fun u => mul_comm _ _)
  have hodd : ∀ u, q (-u) = -q u := by
    intro u
    dsimp [q]
    rw [mul_neg,hχ.even,div_neg]
  have href : (∫ u, q u*f (-u)) = -(∫ u, q u*f u) := by
    have hh := integral_neg_eq_self (fun u => q u*f (-u)) volume
    simp only [hodd,neg_neg,neg_mul,integral_neg] at hh
    exact hh.symm
  have he : (∫ u, (1-χ (μ*u))*pvQuotient f u) =
      2⁻¹*((∫ u, q u*f u)-∫ u, q u*f (-u)) := by
    rw [← integral_sub hi hni,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
    rw [pvQuotient_of_ne f (by simpa only [mem_singleton_iff,mem_compl_iff] using hu)]
    dsimp [q]
    ring
  rw [he,href]
  dsimp [pvTruncation,q]
  ring

theorem tendsto_pvTruncation_of_lipschitz (hχ : IsPVCutoff χ) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) :
    Tendsto (fun μ => pvTruncation χ μ f) atTop (𝓝 (∫ u, pvQuotient f u)) := by
  obtain ⟨C,hC⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hi := integrable_pvQuotient_of_lipschitz hf hL
  have ht : Tendsto (fun μ : ℝ => ∫ u, (1-χ (μ*u))*pvQuotient f u)
      atTop (𝓝 (∫ u, pvQuotient f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (1+C)*‖pvQuotient f u‖) ?_ ?_ (hi.norm.const_mul _) ?_
    · exact Eventually.of_forall fun μ =>
        (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id))).aestronglyMeasurable.mul
          hi.aestronglyMeasurable
    · exact Eventually.of_forall fun μ => Eventually.of_forall fun u => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((norm_sub_le 1 _).trans (by simpa only [norm_one] using add_le_add (le_refl (1 : ℝ)) (hC (μ*u)))) (norm_nonneg _)
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      apply tendsto_const_nhds.congr'
      filter_upwards [hχ.eventually_comp_eq_zero (by simpa only [mem_singleton_iff,mem_compl_iff] using hu)] with μ hμ
      simp only [hμ,sub_zero,one_mul]
  exact ht.congr fun μ => (hχ.pvTruncation_eq_of_integrable hf μ).symm

end IsPVCutoff
end WaveTurbulence.Resonant
