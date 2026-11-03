/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainDiagonal

/-!
# Recentring the second diagonal of the gain Schur test
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The incoming diagonal becomes the outgoing diagonal after gain recentering. -/
theorem lintegral_gain_diagonal_shift {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F f g : Mom d → ℝ} (hF : Measurable F) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal ((F (q.1 + q.2.1)) ^ 2) *
      ENNReal.ofReal |f (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |g (q.1 + q.2.2)|
      ∂volume.prod (resonantMeasure e)) =
    ∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal ((F q.1) ^ 2) *
      ENNReal.ofReal |g (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |f (q.1 + q.2.2)|
      ∂volume.prod (resonantMeasure e) := by
  let H : Mom d × (Mom d × Mom d) → ℝ≥0∞ := fun q => ENNReal.ofReal ((F q.1) ^ 2) *
    ENNReal.ofReal |g (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |f (q.1 + q.2.2)|
  have hH : Measurable H :=
    (((hF.pow_const 2).ennreal_ofReal.comp measurable_fst).mul
      (hg.abs.ennreal_ofReal.comp (by fun_prop))).mul (hf.abs.ennreal_ofReal.comp (by fun_prop))
  calc
    _ = ∫⁻ q, H (gainShift q) ∂volume.prod (resonantMeasure e) := by
      apply lintegral_congr
      rintro ⟨k, a, b⟩
      dsimp only [H, gainShift]
      rw [add_neg_cancel_right]
      ac_rfl
    _ = ∫⁻ q, H q ∂volume.prod (resonantMeasure e) := lintegral_gainShift he hd hH
    _ = _ := rfl

end WaveTurbulence.WKEL2
