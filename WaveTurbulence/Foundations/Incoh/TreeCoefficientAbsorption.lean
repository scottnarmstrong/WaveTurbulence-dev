/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootSpectralMass
public import WaveTurbulence.Foundations.Incoh.RootAmplitudeMass
public import WaveTurbulence.Foundations.Incoh.ExponentialCoefficientAbsorption

/-! # Exponential absorption of the tree root-partition coefficients -/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The spatial mask has no leaf-count dependence at spatial weight zero. -/
theorem maskedSourceSpatialConstant_zero (d m J : ℕ) :
    maskedSourceSpatialConstant d m J 0 = maskedSourceFixedCoefficient d J 0 := by
  simp only [maskedSourceSpatialConstant, maskedSourceFixedCoefficient, pow_zero, mul_one]

/-- Fixed dimensional coefficient of the tree root partition. -/
@[expose] def treeSourceFixedCoefficient (d J : ℕ) : ℝ :=
  rootLocalOverlapConstant d * treeRootAmplitudeDerivativeFactor d J * maskedSourceFixedCoefficient d J 0

/-- Source-independent exponential constant for all actual tree spatial factors. -/
@[expose] def treeSourceExponentialCoefficient (d J K M : ℕ) (B C : ℝ) : ℝ :=
  max 1 (treeSourceFixedCoefficient d J) *
    (max 1 (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B)) ^ 3 *
      max 1 C * (max 1 (halfCellFourierConstant d)) ^ 2

theorem treeSourceExponentialCoefficient_pos (d J K M : ℕ) (B C : ℝ) :
    0 < treeSourceExponentialCoefficient d J K M B C := by
  unfold treeSourceExponentialCoefficient
  positivity

/-- Literal extended-real tree coefficients are bounded exponentially in the source order. -/
theorem tree_source_ennreal_coefficient_le {d J K M n m : ℕ}
    (hn : 1 ≤ n) (hm : m + 1 ≤ 3 * n) {B C C₀ δ r : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    (ENNReal.ofReal (rootLocalOverlapConstant d) *
      (ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J) *
        ENNReal.ofReal (maskedSourceSpatialConstant d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))) *
      ENNReal.ofReal ((C₀ * δ) ^ n * r) ≤
        ENNReal.ofReal (((treeSourceExponentialCoefficient d J K M B C * C₀) * δ) ^ n * r) := by
  have ho : 0 ≤ rootLocalOverlapConstant d := by
    have hrad := treeRootCutoffRadius_nonneg d
    unfold rootLocalOverlapConstant
    positivity
  have ht := treeRootAmplitudeDerivativeFactor_nonneg d J
  have hfixed : 0 ≤ maskedSourceFixedCoefficient d J 0 := by
    rw [← maskedSourceSpatialConstant_zero d 0 J]
    exact maskedSourceSpatialConstant_nonneg _ _ _ _
  have ha : 0 ≤ treeSourceFixedCoefficient d J := mul_nonneg (mul_nonneg ho ht) hfixed
  have hb : 0 ≤ leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg M))
    · exact zero_le_one.trans (le_max_left _ _)
  have hh := (halfCellFourierConstant_pos d).le
  have hcoef := order_coefficient_le_exponential hn hm ha hb hC hh
  change _ ≤ treeSourceExponentialCoefficient d J K M B C ^ n at hcoef
  rw [maskedSourceSpatialConstant_zero]
  have he : ENNReal.ofReal (rootLocalOverlapConstant d) *
      (ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J) *
        ENNReal.ofReal (maskedSourceFixedCoefficient d J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) =
      ENNReal.ofReal (treeSourceFixedCoefficient d J *
        (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) * C ^ n *
          halfCellFourierConstant d ^ (2 * n)) := by
    simp only [treeSourceFixedCoefficient, ENNReal.ofReal_mul ho,
      ENNReal.ofReal_mul (mul_nonneg ho ht), ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ho ht) hfixed),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg ho ht) hfixed) (pow_nonneg hb _)),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ho ht) hfixed) (pow_nonneg hb _)) (pow_nonneg hC _)),
      ENNReal.ofReal_pow hb, ENNReal.ofReal_pow hh]
    ring
  rw [he, ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg hb _)) (pow_nonneg hC _)) (pow_nonneg hh _))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ treeSourceExponentialCoefficient d J K M B C ^ n * ((C₀ * δ) ^ n * r) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg (mul_nonneg hC₀ hδ) _) hr)
    _ = _ := by simp only [mul_pow]; ring

end WaveTurbulence.Incoh
