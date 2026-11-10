/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantReflections

/-!
# The change of variables in the gain Schur test

The involution (k,a,b) ↦ (k+a,-a,b) preserves dk dν(a,b).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Recenter the gain kernel at its first incoming momentum. -/
@[expose] def gainShift (q : Mom d × (Mom d × Mom d)) : Mom d × (Mom d × Mom d) :=
  (q.1 + q.2.1, (-q.2.1, q.2.2))

theorem measurable_gainShift : Measurable (gainShift (d := d)) := by
  unfold gainShift
  fun_prop

/-- Nonnegative change of variables for the full gain Schur measure. -/
theorem lintegral_gainShift {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {H : Mom d × (Mom d × Mom d) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ q, H (gainShift q) ∂volume.prod (resonantMeasure e)) =
      ∫⁻ q, H q ∂volume.prod (resonantMeasure e) := by
  let := resonantMeasure_finiteOnCompacts e hd
  have hcomp : Measurable (fun q : Mom d × (Mom d × Mom d) => H (gainShift q)) :=
    hH.comp measurable_gainShift
  have hK : Measurable (fun p : Mom d × Mom d => ∫⁻ k : Mom d, H (k, p)) :=
    (hH.comp measurable_swap).lintegral_prod_right'
  calc
    _ = ∫⁻ p : Mom d × Mom d, ∫⁻ k : Mom d, H (gainShift (k, p))
        ∂volume ∂resonantMeasure e := lintegral_prod_symm _ hcomp.aemeasurable
    _ = ∫⁻ p : Mom d × Mom d, ∫⁻ k : Mom d, H (k, (-p.1, p.2))
        ∂volume ∂resonantMeasure e := by
      apply lintegral_congr
      intro p
      exact lintegral_add_right_eq_self (fun k : Mom d => H (k, (-p.1, p.2))) p.1
    _ = ∫⁻ p : Mom d × Mom d, ∫⁻ k : Mom d, H (k, p)
        ∂volume ∂resonantMeasure e := lintegral_resonantMeasure_neg_first he hd hK
    _ = _ := (lintegral_prod_symm _ hH.aemeasurable).symm

end WaveTurbulence.WKEL2
