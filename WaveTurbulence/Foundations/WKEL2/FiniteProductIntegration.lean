/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tonelli in head and tail coordinates of a finite real product
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Split Lebesgue integration on a finite coordinate product into its head and tail. -/
theorem lintegral_fin_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ t : ℝ, ∫⁻ y : Fin n → ℝ, F (Fin.cons t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  have hp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).symm
  have heq : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove]
    · simp [e, MeasurableEquiv.piFinSuccAbove]
  have hm : Measurable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) := by
    apply hF.comp
    fun_prop
  calc
    _ = ∫⁻ p : ℝ × (Fin n → ℝ), F (Fin.cons p.1 p.2) := by
      simpa only [heq] using (hp.lintegral_comp hF).symm
    _ = _ := lintegral_prod _ hm.aemeasurable

end WaveTurbulence.WKEL2
