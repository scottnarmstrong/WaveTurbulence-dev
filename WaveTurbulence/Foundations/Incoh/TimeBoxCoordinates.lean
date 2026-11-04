/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.DifferenceBox
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product and two-coordinate time boxes

TARGET (incohproof11): coordinate transport preserves the literal box
measure, before applying the difference-coordinate estimates.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The two-coordinate box is precisely the preimage of the product of scalar intervals. -/
theorem preimage_finTwoArrow_Icc (a b c d : ℝ) :
    MeasurableEquiv.finTwoArrow ⁻¹' (Icc a b ×ˢ Icc c d) = Icc ![a, c] ![b, d] := by
  ext t
  simp only [mem_preimage, MeasurableEquiv.finTwoArrow_apply, mem_prod, mem_Icc,
    Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- Transport the actual two-time box integral to the product coordinates used in Tonelli. -/
theorem setLIntegral_twoTimeBox (a b c d : ℝ) (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ t : Fin 2 → ℝ in Icc ![a, c] ![b, d], f (t 0, t 1)) =
      ∫⁻ z : ℝ × ℝ in Icc a b ×ˢ Icc c d, f z := by
  rw [← preimage_finTwoArrow_Icc]
  exact (volume_preserving_finTwoArrow ℝ).setLIntegral_comp_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding f _

end WaveTurbulence.Incoh
