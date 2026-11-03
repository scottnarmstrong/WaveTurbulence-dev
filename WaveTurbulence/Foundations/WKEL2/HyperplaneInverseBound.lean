/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.InverseConvolution
public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure

/-!
# Uniform inverse-norm bound on moving hyperplanes

The spatial form of M₂ in research-note Lemma 4(a). Project the translated
center onto the hyperplane and use an isometry onto `Mom (d-1)`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Uniform hyperplane convolution bound; the constant depends only on `d,a`. -/
theorem exists_uniform_hyperplane_inverse (hd : 3 ≤ d) (a : ℝ)
    (ha : (d : ℝ) - 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ k : Mom d,
      Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => japaneseDecay a (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹) ∧
      (∫ w : ↥(ℝ ∙ ℓ)ᗮ, japaneseDecay a (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹) ≤ C := by
  have had : ((d - 1 : ℕ) : ℝ) - 1 < a := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    linarith only [ha]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_inverse_convolution
    (d := d - 1) (by omega) a had
  have ha0 : 0 ≤ a := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ha, hdR]
  refine ⟨C, hC, fun ℓ hℓ k => ?_⟩
  let E := perpIsometry hℓ
  let c := perpPart ℓ k
  obtain ⟨hi, hb⟩ := hbound (E c)
  have hipull : Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ =>
      japaneseDecay a (E c + E w) * ‖E w‖⁻¹) :=
    (E.measurePreserving.integrable_comp_emb E.toMeasurableEquiv.measurableEmbedding).mpr hi
  have hchange := E.measurePreserving.integral_comp' (f := E.toMeasurableEquiv)
    (fun x => japaneseDecay a (E c + x) * ‖x‖⁻¹)
  have hnorm (w : ↥(ℝ ∙ ℓ)ᗮ) : ‖((c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖ ≤ ‖k + (w : Mom d)‖ := by
    simpa only [c, zero_smul, add_zero] using norm_perpPart_add_le hℓ k 0 w
  have hweight (w : ↥(ℝ ∙ ℓ)ᗮ) : japaneseDecay a (k + (w : Mom d)) ≤ japaneseDecay a (E c + E w) := by
    rw [japaneseDecay, japaneseDecay, ← E.map_add, E.norm_map]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact add_le_add (le_refl 1) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hnorm w))
    · linarith only [ha0]
  have hp (w : ↥(ℝ ∙ ℓ)ᗮ) :
      japaneseDecay a (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹ ≤
        japaneseDecay a (E c + E w) * ‖E w‖⁻¹ := by
    rw [E.norm_map]
    exact mul_le_mul_of_nonneg_right (hweight w) (inv_nonneg.mpr (norm_nonneg _))
  have hm : Measurable (fun w : ↥(ℝ ∙ ℓ)ᗮ => japaneseDecay a (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹) := by
    have hbase : Continuous (fun w : ↥(ℝ ∙ ℓ)ᗮ => 1 + ‖k + (w : Mom d)‖ ^ 2) := by fun_prop
    exact (hbase.rpow_const (fun _ => Or.inl (by positivity))).measurable.mul
      (measurable_norm.comp measurable_subtype_coe).inv
  have hitarget : Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => japaneseDecay a (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹) := by
    refine hipull.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg
      (mul_nonneg (japaneseDecay_nonneg a _) (inv_nonneg.mpr (norm_nonneg _)))]
    exact hp w
  refine ⟨hitarget, (integral_mono hitarget hipull hp).trans ?_⟩
  exact hchange.le.trans hb

end WaveTurbulence.WKEL2
