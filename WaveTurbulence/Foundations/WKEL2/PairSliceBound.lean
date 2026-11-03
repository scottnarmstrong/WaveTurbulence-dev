/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CodimTwoSliceENN
public import WaveTurbulence.Foundations.WKEL2.TwoAxesExceptional
public import WaveTurbulence.Foundations.WKEL2.ScalarShear

/-!
# The two-direction weighted slice estimate

The Jacobian and transverse-integral step in research-note Proposition 6.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Two scalar samples on nondegenerate directions separate at inverse-sine cost. -/
theorem lintegral_pair_slice_le (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {θ v : Mom d} (hθ : ‖θ‖ = 1)
    (hθ0 : θ ≠ 0) (hη : transverseAxis hθ0 v ≠ 0)
    {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) (k : Mom d) :
    (∫⁻ w : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) *
      F ⟪θ, w⟫_ℝ * G ⟪v, w⟫_ℝ) ≤
      ENNReal.ofReal (transverseDecayMass d s) * ENNReal.ofReal (angularSineInv θ v) *
        (∫⁻ t : ℝ, F t) * ∫⁻ u : ℝ, G u := by
  let η := transverseAxis hθ0 v
  let T := twoAxisSliceEquiv hθ0 hη
  let W : Mom d → ℝ≥0∞ := fun w => ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) *
    F ⟪θ, w⟫_ℝ * G ⟪v, w⟫_ℝ
  have hdec : Measurable (fun w : Mom d => ENNReal.ofReal (japaneseDecay (2 * s) (k + w))) := by
    have hc : Continuous (fun w : Mom d => 1 + ‖k + w‖ ^ 2) := by fun_prop
    exact (hc.rpow_const (fun _ => Or.inl (by positivity))).measurable.ennreal_ofReal
  have hW : Measurable W :=
    (hdec.mul (hF.comp (by fun_prop))).mul (hG.comp (by fun_prop))
  have hiθ (p : ℝ × (ℝ × Mom (d - 1 - 1))) : ⟪θ, T p⟫_ℝ = p.1 := by
    dsimp only [T]
    rw [twoAxisSliceEquiv_apply, codimTwoSlice]
    simpa only [unitVec_of_norm_one hθ] using
      inner_unit_axisSlice hθ0 p.1 (axisSliceEquiv hη p.2)
  have hiv (p : ℝ × (ℝ × Mom (d - 1 - 1))) :
      ⟪v, T p⟫_ℝ = p.1 * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * p.2.1 :=
    inner_codimTwoSlice hθ0 hη p.1 p.2.1 p.2.2
  have hchange := (measurePreserving_twoAxisSliceEquiv hθ0 hη).lintegral_comp_emb
    T.measurableEmbedding W
  have hcomp : Measurable (fun p : ℝ × (ℝ × Mom (d - 1 - 1)) => W (T p)) := hW.comp T.measurable
  have hslice (t u : ℝ) :
      (∫⁻ z : Mom (d - 1 - 1), W (T (t, (u, z)))) ≤
        ENNReal.ofReal (transverseDecayMass d s) * F t *
          G (t * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * u) := by
    have hm : Measurable (fun z : Mom (d - 1 - 1) =>
        ENNReal.ofReal (japaneseDecay (2 * s) (k + T (t, (u, z))))) :=
      hdec.comp (T.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    simp only [W, hiθ, hiv]
    rw [lintegral_mul_const _ (hm.mul_const _), lintegral_mul_const _ hm]
    exact mul_le_mul' (mul_le_mul' (lintegral_codimTwoSlice_le hd s hs hθ0 hη k t u) le_rfl) le_rfl
  have hscalar : Measurable (fun p : ℝ × ℝ => F p.1 *
      G (p.1 * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * p.2)) :=
    (hF.comp measurable_fst).mul (hG.comp (by fun_prop))
  calc
    _ = ∫⁻ p : ℝ × (ℝ × Mom (d - 1 - 1)), W (T p) ∂volume.prod (volume.prod volume) := hchange.symm
    _ = ∫⁻ t : ℝ, ∫⁻ u : ℝ, ∫⁻ z : Mom (d - 1 - 1), W (T (t, (u, z))) := by
      rw [lintegral_prod _ hcomp.aemeasurable]
      apply lintegral_congr
      intro t
      exact lintegral_prod _ (hcomp.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ ≤ ∫⁻ t : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (transverseDecayMass d s) * F t *
        G (t * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * u) :=
      lintegral_mono fun t => lintegral_mono (hslice t)
    _ = ENNReal.ofReal (transverseDecayMass d s) *
        ∫⁻ t : ℝ, ∫⁻ u : ℝ, F t * G (t * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * u) := by
      simp_rw [mul_assoc]
      have hscalar_t (t : ℝ) : Measurable (fun u : ℝ => F t *
          G (t * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * u)) :=
        hscalar.comp (measurable_const.prodMk measurable_id)
      have hmean : Measurable (fun t : ℝ => ∫⁻ u : ℝ,
          F t * G (t * ⟪v, unitVec θ⟫_ℝ + ‖η‖ * u)) := hscalar.lintegral_prod_right'
      simp_rw [lintegral_const_mul _ (hscalar_t _)]
      rw [lintegral_const_mul _ hmean]
    _ = _ := by
      have hηpos : 0 < ‖η‖ := norm_pos_iff.mpr hη
      have hshear := lintegral_scalar_shear_product hF hG ⟪v, unitVec θ⟫_ℝ ‖η‖ hηpos
      simp only [mul_comm ⟪v, unitVec θ⟫_ℝ] at hshear
      rw [hshear]
      rw [inv_norm_transverseAxis hθ0 v]
      ac_rfl

end WaveTurbulence.WKEL2
