/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceExitTransform

/-!
# Joint measurability and the coincident-coordinate sparse transform

The sparse transform is jointly measurable in its two frequencies.
When the selected coordinate is the distinguished first time, it
depends only on the difference of those frequencies, exactly as in
the one-exit positive endpoint estimate.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The sparse endpoint transform is jointly measurable in both frequencies. -/
theorem measurable_sourceExitTransform {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F) (c h : ℝ) :
    Measurable (fun ξ : ℝ × ℝ => sourceExitTransform D hI upper v F c h ξ.1 ξ.2) := by
  have hc : Continuous (fun q : (ℝ × ℝ) × (D.S.TVar → ℝ) =>
      sourceExitPhase D hI v q.1.1 q.1.2 q.2) := by
    unfold sourceExitPhase
    simp_rw [Real.fourierChar_apply]
    fun_prop
  have ha := (measurable_sourceExitAmplitude D hI upper v F hF).comp
    (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × (D.S.TVar → ℝ) → _))
  have hm := (ha.mul hc.measurable).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (localInputTimeDomain D c h))
  exact hm.measurable

/-- The coincident selected coordinate gives a one-frequency transform of the actual amplitude. -/
theorem sourceExitTransform_first_eq_difference {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (F : (D.S.TVar → ℝ) → ℂ) (c h α ζ : ℝ) :
    sourceExitTransform D hI upper (firstTime D hI) F c h α ζ =
      sourceExitTransform D hI upper (firstTime D hI) F c h 0 (ζ-α) := by
  unfold sourceExitTransform
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact congrArg (fun x : ℝ => sourceExitAmplitude D hI upper (firstTime D hI) F u*
    (Real.fourierChar x:ℂ)) (by ring : α*u (firstTime D hI)-ζ*u (firstTime D hI) =
      0*u (firstTime D hI)-(ζ-α)*u (firstTime D hI))

end WaveTurbulence.SumintPar
