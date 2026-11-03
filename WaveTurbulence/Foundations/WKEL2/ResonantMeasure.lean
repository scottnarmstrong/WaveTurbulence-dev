/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.HyperplaneChart

/-!
# Resonant measure from fixed hyperplane coordinates

The measure here includes `|a|⁻¹` and omits the collision operator's factor 1/2,
matching Lemma 1 of `docs/research/git20-general-d.md`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance referenceMeasureSpace (e : Mom d) : MeasureSpace ↥(ℝ ∙ e)ᗮ :=
  measureSpaceOfInnerProductSpace
local instance referenceBorelSpace (e : Mom d) : BorelSpace ↥(ℝ ∙ e)ᗮ := inferInstance

/-- Joint chart from the fixed reference hyperplane to resonant pairs. -/
@[expose] noncomputable def resonantChart (e : Mom d)
    (p : Mom d × ↥(ℝ ∙ e)ᗮ) : Mom d × Mom d :=
  (p.1, normalReflection e p.1 p.2)

/-- Measurable inclusion of the reference coordinates into two ambient vectors. -/
theorem measurable_referenceCoordinates (e : Mom d) :
    Measurable (fun p : Mom d × ↥(ℝ ∙ e)ᗮ => (p.1, (p.2 : Mom d))) := by
  have h : Continuous (fun w : ↥(ℝ ∙ e)ᗮ => (w : Mom d)) := continuous_subtype_val
  exact measurable_fst.prodMk (h.measurable.comp measurable_snd)

/-- Measurable ambient graph, before restricting the second coordinate. -/
theorem measurable_normalReflection_graph (e : Mom d) :
    Measurable (fun p : Mom d × Mom d => (p.1, normalReflection e p.1 p.2)) :=
  measurable_fst.prodMk (measurable_normalReflection e)

/-- The joint chart is measurable, including its exceptional directions. -/
theorem measurable_resonantChart (e : Mom d) : Measurable (resonantChart e) :=
  (measurable_normalReflection_graph e).comp (measurable_referenceCoordinates e)

/-- The resonant measure constructed as a pushforward of a weighted product.
For a unit reference vector, the integral formula below identifies this with
the intrinsic hyperplane measure, independently of the reference vector. -/
@[expose] noncomputable def resonantMeasure (e : Mom d) : Measure (Mom d × Mom d) :=
  Measure.map (resonantChart e)
    ((volume.prod volume).withDensity (fun p : Mom d × ↥(ℝ ∙ e)ᗮ =>
      ENNReal.ofReal (‖p.1‖⁻¹)))

/-- Nonnegative Borel integration against the resonant measure in fixed coordinates. -/
theorem lintegral_resonantMeasure_chart (e : Mom d) {F : Mom d × Mom d → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂resonantMeasure e =
      ∫⁻ a : Mom d, ENNReal.ofReal (‖a‖⁻¹) *
        ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w) := by
  rw [resonantMeasure, lintegral_map hF (measurable_resonantChart e),
    lintegral_withDensity_eq_lintegral_mul (volume.prod volume)
      (f := fun p : Mom d × ↥(ℝ ∙ e)ᗮ => ENNReal.ofReal (‖p.1‖⁻¹))
      (g := fun p => F (resonantChart e p))
      ((measurable_norm.comp measurable_fst).inv.ennreal_ofReal)
      (hF.comp (measurable_resonantChart e))]
  have hdens : Measurable (fun p : Mom d × ↥(ℝ ∙ e)ᗮ =>
      ENNReal.ofReal (‖p.1‖⁻¹)) :=
    ((measurable_norm.comp measurable_fst).inv.ennreal_ofReal)
  have hG := hdens.mul (hF.comp (measurable_resonantChart e))
  change ∫⁻ p, ENNReal.ofReal (‖p.1‖⁻¹) * F (resonantChart e p) ∂volume.prod volume = _
  have hprod := lintegral_prod
    (fun p : Mom d × ↥(ℝ ∙ e)ᗮ => ENNReal.ofReal (‖p.1‖⁻¹) * F (resonantChart e p))
    (μ := volume) (ν := volume) hG.aemeasurable
  rw [hprod]
  apply lintegral_congr
  intro a
  exact lintegral_const_mul (μ := volume) (ENNReal.ofReal (‖a‖⁻¹))
    (hF.comp (continuous_const.prodMk
      ((normalReflection e a).continuous.comp continuous_subtype_val)).measurable)

/-- The intrinsic nonnegative hyperplane integral depends measurably on its normal. -/
theorem measurable_lintegral_hyperplane {e : Mom d} (he : ‖e‖ = 1)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a : Mom d => ∫⁻ w : ↥(ℝ ∙ a)ᗮ, F (a, w)) := by
  have hm : Measurable (fun a : Mom d =>
      ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w)) :=
    (hF.comp (measurable_resonantChart e)).lintegral_prod_right'
  have hi : (fun a : Mom d => ∫⁻ w : ↥(ℝ ∙ a)ᗮ, F (a, w)) =
      ({0} : Set (Mom d)).piecewise
        (fun _ => ∫⁻ w : ↥(ℝ ∙ (0 : Mom d))ᗮ, F (0, w))
        (fun a => ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w)) := by
    funext a
    by_cases ha : a = 0
    · subst a
      simp only [Set.piecewise, mem_singleton_iff, ↓reduceIte]
    · simp only [Set.piecewise, mem_singleton_iff, ha, ↓reduceIte]
      exact lintegral_hyperplaneChart he ha (fun x => F (a, x))
  rw [hi]
  exact measurable_const.piecewise (measurableSet_singleton 0) hm

/-- Intrinsic hyperplane formula for every nonnegative Borel kernel (Lemma 1's measure). -/
theorem lintegral_resonantMeasure {e : Mom d} (he : ‖e‖ = 1)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂resonantMeasure e =
      ∫⁻ a : Mom d, ENNReal.ofReal (‖a‖⁻¹) * ∫⁻ w : ↥(ℝ ∙ a)ᗮ, F (a, w) := by
  rw [lintegral_resonantMeasure_chart e hF]
  apply lintegral_congr
  intro a
  by_cases ha : a = 0
  · subst a
    simp only [norm_zero, inv_zero, ENNReal.ofReal_zero, zero_mul]
  · rw [lintegral_hyperplaneChart he ha (fun x => F (a, x))]

end WaveTurbulence.WKEL2
