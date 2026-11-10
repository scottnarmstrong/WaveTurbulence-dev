/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ShortTimeProfile
public import WaveTurbulence.Foundations.Incoh.LayerLink
public import WaveTurbulence.Foundations.Incoh.UnitOrientation
public import WaveTurbulence.Foundations.Incoh.TimeBoxCoordinates

/-!
# Short-time estimates on the literal layered link boxes

TARGET (incohproof14)–(incohproof15). The same dimensional constant
bounds the coherent and incoherent cases; the latter gains a full inverse
time-frequency scale from the integer-layer geometry.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal short-frequency part of the link on its two-time box. -/
@[expose] def shortLinkTimeProfile {d : ℕ} (L lam : ℝ) (Q : LayerLink d)
    (t : Fin 2 → ℝ) : ℝ≥0∞ :=
  shortLinkProfile L Q.toLinkParameters (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1))

private theorem scalar_layer_separation {a b : ℤ} (hab : a ≠ b) :
    ∃ q : ℝ,
      ((∀ x ∈ Icc (a : ℝ) (a + 1), x ≤ q) ∧ (∀ y ∈ Icc (b : ℝ) (b + 1), q ≤ y)) ∨
      ((∀ x ∈ Icc (a : ℝ) (a + 1), q ≤ x) ∧ (∀ y ∈ Icc (b : ℝ) (b + 1), y ≤ q)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hc : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    exact ⟨b, Or.inl ⟨fun _ hx => hx.2.trans hc, fun _ hy => hy.1⟩⟩
  · have hc : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    exact ⟨a, Or.inr ⟨fun _ hx => hx.1, fun _ hy => hy.2.trans hc⟩⟩

/-- TARGET (incohproof14)–(incohproof15), before substituting `lam = δ L^(2γ)`. -/
theorem exists_shortTime_box_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ lam : ℝ, 0 < lam → ∀ Q : LayerLink d,
      (∫⁻ t in linkBox Q, shortLinkTimeProfile L lam Q t) ≤
        ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (C * L ^ (2 * d)) ∧
      (Q.IsIncoherent → (∫⁻ t in linkBox Q, shortLinkTimeProfile L lam Q t) ≤
        (ENNReal.ofReal lam⁻¹) ^ 2 * ENNReal.ofReal (C * L ^ (2 * d))) := by
  obtain ⟨C, hC, hb⟩ := exists_shortLinkProfile_moments_bound d hd
  refine ⟨C, hC, ?_⟩
  intro L hL lam hlam Q
  let I := Icc (Q.leftLayer : ℝ) ((Q.leftLayer : ℝ) + 1)
  let J := Icc (Q.rightLayer : ℝ) ((Q.rightLayer : ℝ) + 1)
  let f : ℝ → ℝ≥0∞ := fun r => shortLinkProfile L Q.toLinkParameters ((((-Q.orientation) : ℤ) : ℝ) * r)
  have hf : Measurable f := (measurable_shortLinkProfile (zero_lt_one.trans_le hL) Q.toLinkParameters).comp
    (measurable_const.mul measurable_id)
  have hmass₀ : (∫⁻ r, f r) ≤ ENNReal.ofReal (C * L ^ (2 * d)) := by
    simpa only [f, Units.val_neg] using
      (lintegral_intUnit_mul (-Q.orientation) (shortLinkProfile L Q.toLinkParameters)).le.trans
        (hb L hL Q.toLinkParameters).1
  have hmass₁ : (∫⁻ r, f r * ENNReal.ofReal |r|) ≤ ENNReal.ofReal (C * L ^ (2 * d)) := by
    simpa only [f, Units.val_neg] using
      (lintegral_firstMoment_intUnit_mul (-Q.orientation) (shortLinkProfile L Q.toLinkParameters)).le.trans
        (hb L hL Q.toLinkParameters).2
  have hcoord : (∫⁻ t in linkBox Q, shortLinkTimeProfile L lam Q t) =
      ∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => f (lam * (z.2 - z.1))) z := by
    rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
    calc
      _ = ∫⁻ t in linkBox Q, f (lam * (t 1 - t 0)) := by
        apply lintegral_congr
        intro t
        change shortLinkProfile L Q.toLinkParameters _ = shortLinkProfile L Q.toLinkParameters _
        congr 1
        simp only [Int.cast_neg]
        ring
      _ = _ := setLIntegral_twoTimeBox _ _ _ _ (fun z => f (lam * (z.2 - z.1)))
  rw [hcoord]
  constructor
  · have hvol : volume I ≤ 1 := by
      dsimp only [I]
      rw [Real.volume_Icc, add_sub_cancel_left]
      norm_num
    exact (lintegral_scaled_difference_box_le measurableSet_Icc measurableSet_Icc hvol hlam hf).trans
      (mul_le_mul' le_rfl hmass₀)
  · intro hQ
    obtain ⟨q, hsep⟩ := scalar_layer_separation (show Q.leftLayer ≠ Q.rightLayer from hQ)
    exact (lintegral_scaled_difference_box_le_firstMoment measurableSet_Icc measurableSet_Icc hsep hlam hf).trans
      (mul_le_mul' le_rfl hmass₁)

end WaveTurbulence.Incoh
