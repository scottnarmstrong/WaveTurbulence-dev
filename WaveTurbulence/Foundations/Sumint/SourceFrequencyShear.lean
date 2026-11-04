/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTimeShearMeasure
public import WaveTurbulence.Foundations.Fourier.TimeFourier

/-!
# The frequency shear dual to source time differences

The Fourier change of variables adds the last two frequencies to the
first one. Its inverse is the corresponding scalar translation.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The inverse transpose of the source time shear. -/
@[expose] def sourceFrequencyShear (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![ξ 0+ξ 1+ξ 2,ξ 1,ξ 2]

/-- The inverse frequency change. -/
@[expose] def sourceFrequencyUnshear (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![ξ 0-ξ 1-ξ 2,ξ 1,ξ 2]

@[simp] theorem sourceFrequencyShear_unshear (ξ : Fin 3 → ℝ) :
    sourceFrequencyShear (sourceFrequencyUnshear ξ) = ξ := by
  ext j
  fin_cases j <;> simp [sourceFrequencyShear,sourceFrequencyUnshear]
  ring

@[simp] theorem sourceFrequencyUnshear_shear (ξ : Fin 3 → ℝ) :
    sourceFrequencyUnshear (sourceFrequencyShear ξ) = ξ := by
  ext j
  fin_cases j <;> simp [sourceFrequencyShear,sourceFrequencyUnshear]
  ring

/-- The frequency shear is a measurable equivalence. -/
@[expose] def sourceFrequencyShearEquiv : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun := sourceFrequencyShear
  invFun := sourceFrequencyUnshear
  left_inv := sourceFrequencyUnshear_shear
  right_inv := sourceFrequencyShear_unshear
  measurable_toFun := by
    change Measurable sourceFrequencyShear
    unfold sourceFrequencyShear
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> fun_prop
  measurable_invFun := by
    change Measurable sourceFrequencyUnshear
    unfold sourceFrequencyUnshear
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> fun_prop

/-- The frequency shear preserves native Lebesgue measure. -/
theorem measurePreserving_sourceFrequencyShear : MeasurePreserving sourceFrequencyShear := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodComm (α := ℝ) (β := Fin 2 → ℝ))
  have hs : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ) := by
    rw [Measure.volume_eq_prod,Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have he : MeasurePreserving e := hs.comp (volume_preserving_piFinSuccAbove _ _)
  have hp : MeasurePreserving
      (fun p : (Fin 2 → ℝ) × ℝ => (p.1,p.2+p.1 0+p.1 1)) := by
    rw [Measure.volume_eq_prod]
    have hm : Measurable (Function.uncurry (fun (a : Fin 2 → ℝ) (b : ℝ) =>
        b+a 0+a 1)) := by fun_prop
    have ht : ∀ a : Fin 2 → ℝ, MeasurePreserving (fun b : ℝ => b+a 0+a 1) := by
      intro a
      convert measurePreserving_add_right volume (a 0+a 1) using 1
      funext b
      ring
    exact (MeasurePreserving.id (volume : Measure (Fin 2 → ℝ))).skew_product hm
      (ae_of_all _ (fun a => (ht a).map_eq))
  have hc := (he.symm e).comp (hp.comp he)
  convert hc using 1
  funext ξ
  apply e.injective
  simp only [Function.comp_apply,e.apply_symm_apply]
  apply Prod.ext
  · ext j
    fin_cases j <;> rfl
  · rfl

/-- The dual pairing transforms by the inverse transpose. -/
theorem timePairing_unshear (z ξ : Fin 3 → ℝ) :
    Fourier.timePairing 3 (sourceTimeUnshear z) ξ =
      Fourier.timePairing 3 z (sourceFrequencyShear ξ) := by
  change (∑ j, sourceTimeUnshear z j * ξ j) =
    ∑ j, z j * sourceFrequencyShear ξ j
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  change z 0*ξ 0+(z 1+z 0)*ξ 1+(z 2+z 0)*ξ 2 =
    z 0*(ξ 0+ξ 1+ξ 2)+z 1*ξ 1+z 2*ξ 2
  ring

end WaveTurbulence.Sumint
