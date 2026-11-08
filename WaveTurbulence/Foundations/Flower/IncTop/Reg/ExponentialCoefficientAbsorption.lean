/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellEnvelope
import Mathlib.Tactic.Ring

/-! Ported by source from C2-B-TOP `Cut2BReg.ExponentialCoefficientAbsorption` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Absorbing explicit source localization coefficients into an exponential order constant -/

public section
noncomputable section

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Every nonnegative coefficient with at most `3n` input factors has a fixed exponential bound. -/
theorem order_coefficient_le_exponentialSpatial {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ 3 * n)
    {a b c h : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hh : 0 ≤ h) :
    a * b ^ m * c ^ n * h ^ (2 * n) ≤
      (max 1 a * (max 1 b) ^ 3 * max 1 c * (max 1 h) ^ 2) ^ n := by
  have ha' : a ≤ (max 1 a) ^ n :=
    (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hb' : b ^ m ≤ (max 1 b) ^ (3 * n) :=
    (pow_le_pow_left₀ hb (le_max_right _ _) m).trans (pow_le_pow_right₀ (le_max_left _ _) hm)
  have hc' := pow_le_pow_left₀ hc (le_max_right 1 c) n
  have hh' := pow_le_pow_left₀ hh (le_max_right 1 h) (2 * n)
  calc
    _ ≤ (max 1 a) ^ n * (max 1 b) ^ (3 * n) * (max 1 c) ^ n * (max 1 h) ^ (2 * n) :=
      mul_le_mul
        (mul_le_mul (mul_le_mul ha' hb' (pow_nonneg hb _) (by positivity)) hc'
          (pow_nonneg hc _) (by positivity)) hh' (pow_nonneg hh _) (by positivity)
    _ = _ := by simp only [mul_pow, pow_mul]

/-- The part of the source mask coefficient independent of the leaf count. -/
@[expose] def maskedSourceFixedCoefficientSpatial (d J W : ℕ) : ℝ :=
  ((2 : ℝ) ^ J * rootMaskDerivativeConstant d J * (2 * Real.pi) ^ J) * (1 + 2 * Real.sqrt d) ^ W

/-- Fixed dimensional source coefficient after the relation `m≤3n` is used. -/
@[expose] def maskedSourceExponentialCoefficientSpatial (d J M W : ℕ) (B C : ℝ) : ℝ :=
  max 1 (maskedSourceFixedCoefficientSpatial d J W) *
    (max 1 ((2 + Real.sqrt d) ^ W * leafWeightedMomentLocalizationConstant d J M W * B)) ^ 3 *
      max 1 C * (max 1 (halfCellFourierConstant d)) ^ 2

theorem maskedSourceExponentialCoefficient_posSpatial (d J M W : ℕ) (B C : ℝ) :
    0 < maskedSourceExponentialCoefficientSpatial d J M W B C := by
  unfold maskedSourceExponentialCoefficientSpatial
  positivity

/-- Literal masked source coefficients satisfy an exponential bound independent of the source
order, leaf centers and input functions. -/
theorem masked_source_coefficient_le_exponentialSpatial {d J M W n m : ℕ}
    (hn : 1 ≤ n) (hm : m ≤ 3 * n) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    maskedSourceSpatialConstantSpatial d m J W * C ^ n *
        ((leafWeightedMomentLocalizationConstant d J M W * B) ^ m * (halfCellFourierConstant d) ^ (2 * n)) ≤
      maskedSourceExponentialCoefficientSpatial d J M W B C ^ n := by
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  have hA : 0 ≤ leafWeightedMomentLocalizationConstant d J M W := by
    unfold leafWeightedMomentLocalizationConstant
    exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _)
      (tsum_nonneg (fun c => cellCenterWeight_nonneg _ c))
  have hfixed : 0 ≤ maskedSourceFixedCoefficientSpatial d J W := by
    unfold maskedSourceFixedCoefficientSpatial
    positivity
  have h := order_coefficient_le_exponentialSpatial hn hm hfixed
    (show 0 ≤ (2 + Real.sqrt d) ^ W * leafWeightedMomentLocalizationConstant d J M W * B by positivity)
    hC (halfCellFourierConstant_pos d).le
  change _ ≤ maskedSourceExponentialCoefficientSpatial d J M W B C ^ n at h
  convert h using 1
  unfold maskedSourceSpatialConstantSpatial maskedSourceFixedCoefficientSpatial
  have hp : ((2 + Real.sqrt (d : ℝ)) ^ m) ^ W = ((2 + Real.sqrt (d : ℝ)) ^ W) ^ m := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm m W]
  simp only [mul_pow, hp]
  ring

/-- The literal extended-real source coefficient is absorbed into the same exponential rate. -/
theorem masked_source_ennreal_coefficient_leSpatial {d J M W n m : ℕ}
    (hn : 1 ≤ n) (hm : m ≤ 3 * n) {B C C₀ δ r : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    (ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J W) * ENNReal.ofReal (C ^ n) *
      (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
        ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
      ENNReal.ofReal ((C₀ * δ) ^ n * r) ≤
        ENNReal.ofReal (((maskedSourceExponentialCoefficientSpatial d J M W B C * C₀) * δ) ^ n * r) := by
  have hA : 0 ≤ leafWeightedMomentLocalizationConstant d J M W * B := by
    apply mul_nonneg _ hB
    unfold leafWeightedMomentLocalizationConstant
    exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _)
      (tsum_nonneg (fun c => cellCenterWeight_nonneg _ c))
  have hmask := maskedSourceSpatialConstant_nonnegSpatial d m J W
  have hhalf := (halfCellFourierConstant_pos d).le
  have hcoef : 0 ≤ maskedSourceSpatialConstantSpatial d m J W * C ^ n *
      ((leafWeightedMomentLocalizationConstant d J M W * B) ^ m * (halfCellFourierConstant d) ^ (2 * n)) :=
    mul_nonneg (mul_nonneg hmask (pow_nonneg hC _)) (mul_nonneg (pow_nonneg hA _) (pow_nonneg hhalf _))
  rw [← ENNReal.ofReal_pow hA, ← ENNReal.ofReal_pow hhalf,
    ← ENNReal.ofReal_mul hmask, ← ENNReal.ofReal_mul (pow_nonneg hA m),
    ← ENNReal.ofReal_mul (mul_nonneg hmask (pow_nonneg hC n)), ← ENNReal.ofReal_mul hcoef]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ maskedSourceExponentialCoefficientSpatial d J M W B C ^ n * ((C₀ * δ) ^ n * r) :=
      mul_le_mul_of_nonneg_right (masked_source_coefficient_le_exponentialSpatial hn hm hB hC)
        (mul_nonneg (pow_nonneg (mul_nonneg hC₀ hδ) _) hr)
    _ = _ := by simp only [mul_pow]; ring

end WaveTurbulence.Flower.IncTop