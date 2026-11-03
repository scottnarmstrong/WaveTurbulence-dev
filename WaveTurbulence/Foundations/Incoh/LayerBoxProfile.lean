/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink
public import WaveTurbulence.Foundations.Incoh.UnitOrientation
public import WaveTurbulence.Foundations.Incoh.TimeBoxCoordinates

/-!
# Nonnegative profiles on a layered link box

TARGET (incohproof13)–(incohproof15): transport any measurable frequency
profile to the literal oriented box. Estimates are proved from Tonelli,
not stored in the link carrier.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The zeroth-moment time-box bound for any measurable nonnegative frequency profile. -/
theorem lintegral_layerBox_profile_le {d : ℕ} (Q : LayerLink d) {lam : ℝ} (hlam : 0 < lam)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t in linkBox Q, f (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1))) ≤
      ENNReal.ofReal lam⁻¹ * ∫⁻ r, f r := by
  let I := Icc (Q.leftLayer : ℝ) ((Q.leftLayer : ℝ) + 1)
  let J := Icc (Q.rightLayer : ℝ) ((Q.rightLayer : ℝ) + 1)
  let g : ℝ → ℝ≥0∞ := fun r => f ((((-Q.orientation) : ℤ) : ℝ) * r)
  have hg : Measurable g := hf.comp (measurable_const.mul measurable_id)
  have hvol : volume I ≤ 1 := by
    dsimp only [I]
    rw [Real.volume_Icc, add_sub_cancel_left]
    norm_num
  have hcoord : (∫⁻ t in linkBox Q, f (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1))) =
      ∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => g (lam * (z.2 - z.1))) z := by
    rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
    calc
      _ = ∫⁻ t in linkBox Q, g (lam * (t 1 - t 0)) := by
        apply lintegral_congr
        intro t
        change f _ = f _
        congr 1
        simp only [Int.cast_neg]
        ring
      _ = _ := setLIntegral_twoTimeBox _ _ _ _ (fun z => g (lam * (z.2 - z.1)))
  have hmass : (∫⁻ r, g r) = ∫⁻ r, f r := by
    simpa only [g, Units.val_neg] using lintegral_intUnit_mul (-Q.orientation) f
  rw [hcoord]
  exact (lintegral_scaled_difference_box_le measurableSet_Icc measurableSet_Icc hvol hlam hg).trans_eq
    (congrArg (fun m => ENNReal.ofReal lam⁻¹ * m) hmass)

/-- Absolute time separation is controlled by the difference of the two integer layers. -/
theorem abs_timeDifference_le {d : ℕ} (Q : LayerLink d) {t : Fin 2 → ℝ} (ht : t ∈ linkBox Q) :
    |t 0 - t 1| ≤ |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 := by
  have hl₀ : (Q.leftLayer : ℝ) ≤ t 0 := ht.1 0
  have hr₀ : (Q.rightLayer : ℝ) ≤ t 1 := ht.1 1
  have hl₁ : t 0 ≤ (Q.leftLayer : ℝ) + 1 := ht.2 0
  have hr₁ : t 1 ≤ (Q.rightLayer : ℝ) + 1 := ht.2 1
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs ((Q.leftLayer : ℝ) - Q.rightLayer)]
  · linarith [le_abs_self ((Q.leftLayer : ℝ) - Q.rightLayer)]

end WaveTurbulence.Incoh
