/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeShear
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Volume preservation of the source time shear

Split off the first time coordinate. The remaining two coordinates
undergo a translation depending measurably on the first coordinate.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- The source shear as a measurable equivalence. -/
@[expose] def sourceTimeShearEquiv : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun := sourceTimeShear
  invFun := sourceTimeUnshear
  left_inv := sourceTimeUnshear_shear
  right_inv := sourceTimeShear_unshear
  measurable_toFun := by
    change Measurable sourceTimeShear
    unfold sourceTimeShear
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> fun_prop [sourceTimeShear]
  measurable_invFun := by
    change Measurable sourceTimeUnshear
    unfold sourceTimeUnshear
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> fun_prop [sourceTimeUnshear]

/-- The source shear preserves native three-dimensional Lebesgue measure. -/
theorem measurePreserving_sourceTimeShear : MeasurePreserving sourceTimeShear := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ _
  have hp : MeasurePreserving
      (fun p : ℝ × (Fin 2 → ℝ) => (p.1, fun j => p.2 j-p.1)) := by
    rw [Measure.volume_eq_prod]
    have hm : Measurable (Function.uncurry (fun (a : ℝ) (b : Fin 2 → ℝ) =>
        fun j => b j-a)) := by
      apply measurable_pi_iff.mpr
      intro j
      exact ((measurable_pi_apply j).comp measurable_snd).sub measurable_fst
    have ht : ∀ a : ℝ, MeasurePreserving (fun b : Fin 2 → ℝ => fun j => b j-a) := by
      intro a
      exact measurePreserving_add_right volume (fun _ : Fin 2 => -a)
    exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product hm
      (ae_of_all _ (fun a => (ht a).map_eq))
  have hc := (he.symm e).comp (hp.comp he)
  convert hc using 1
  funext t
  apply e.injective
  simp only [Function.comp_apply, e.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j <;> rfl

end WaveTurbulence.SumintPar
