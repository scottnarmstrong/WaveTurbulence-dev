/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FrequencyProductMoment
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Translation of a factorized frequency density costs one moment -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- Modulating every independent cell costs only the first moment of its
actual total shift, rather than a product of shift weights. -/
theorem lintegral_shifted_frequency_moment_le {ι : Type*} [Fintype ι] {d : ℕ}
    (β : ι → EuclideanSpace ℝ (Fin d))
    (f : ι → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ ξ : ι → EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+∑ i, ‖ξ i‖) *
      ∏ i, f i (ξ i-β i)) ≤
      ENNReal.ofReal (1+∑ i, ‖β i‖) *
        ∏ i, ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+‖ξ‖) * f i ξ := by
  classical
  let F := fun ξ : ι → EuclideanSpace ℝ (Fin d) =>
    ENNReal.ofReal (1+∑ i, ‖ξ i‖) * ∏ i, f i (ξ i-β i)
  have he := lintegral_add_right_eq_self (μ := (volume : Measure (ι → EuclideanSpace ℝ (Fin d)))) F β
  change (∫⁻ ξ, F ξ) ≤ _
  rw [← he]
  change (∫⁻ ξ : ι → EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+∑ i, ‖ξ i+β i‖) *
    ∏ i, f i (ξ i+β i-β i)) ≤ _
  simp only [add_sub_cancel_right]
  calc
    _ ≤ ∫⁻ ξ : ι → EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+∑ i, ‖β i‖) *
        (ENNReal.ofReal (1+∑ i, ‖ξ i‖) * ∏ i, f i (ξ i)) := by
      apply lintegral_mono
      intro ξ
      have hs : (∑ i, ‖ξ i+β i‖) ≤ (∑ i, ‖ξ i‖)+(∑ i, ‖β i‖) :=
        (Finset.sum_le_sum (fun i _ => norm_add_le _ _)).trans_eq (Finset.sum_add_distrib)
      have hξ : 0 ≤ ∑ i, ‖ξ i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hβ : 0 ≤ ∑ i, ‖β i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hh : 1+∑ i, ‖ξ i+β i‖ ≤ (1+∑ i, ‖β i‖)*(1+∑ i, ‖ξ i‖) := by
        nlinarith [mul_nonneg hξ hβ]
      have hm := ENNReal.ofReal_le_ofReal hh
      rw [ENNReal.ofReal_mul (by positivity)] at hm
      simpa only [mul_assoc] using mul_le_mul' hm (le_refl (∏ i, f i (ξ i)))
    _ = ENNReal.ofReal (1+∑ i, ‖β i‖) *
        ∫⁻ ξ : ι → EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+∑ i, ‖ξ i‖) * ∏ i, f i (ξ i) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl
      (lintegral_sum_frequency_moment_le (fun ξ : EuclideanSpace ℝ (Fin d) => ‖ξ‖)
        measurable_norm (fun ξ => norm_nonneg ξ) f hf)

/-- The same estimate in the two-array product measure used by NT. -/
theorem lintegral_shifted_pair_frequency_moment_le {n d : ℕ}
    (β γ : Fin n → EuclideanSpace ℝ (Fin d))
    (f g : Fin n → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ z : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)),
      ENNReal.ofReal (1+((∑ i, ‖z.1 i‖)+(∑ i, ‖z.2 i‖))) *
        ((∏ i, f i (z.1 i-β i))*(∏ i, g i (z.2 i-γ i)))) ≤
      ENNReal.ofReal (1+((∑ i, ‖β i‖)+(∑ i, ‖γ i‖))) *
        ((∏ i, ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+‖ξ‖)*f i ξ) *
          (∏ i, ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+‖ξ‖)*g i ξ)) := by
  classical
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin n => EuclideanSpace ℝ (Fin d))
  let H := fun z : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
    ENNReal.ofReal (1+((∑ i, ‖z.1 i‖)+(∑ i, ‖z.2 i‖))) *
      ((∏ i, f i (z.1 i-β i))*(∏ i, g i (z.2 i-γ i)))
  have hm := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin n => EuclideanSpace ℝ (Fin d))
  have he := hm.lintegral_comp_emb e.measurableEmbedding H
  change (∫⁻ z, H z) ≤ _
  rw [← he]
  have hmeas (i : Fin n ⊕ Fin n) : Measurable (Sum.elim f g i) := by
    cases i with
    | inl i => exact hf i
    | inr i => exact hg i
  have hh := lintegral_shifted_frequency_moment_le (Sum.elim β γ) (Sum.elim f g) hmeas
  simpa only [H,e,MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi_apply,
    Fintype.sum_sum_type,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr] using hh

end WaveTurbulence.RegAsymp
