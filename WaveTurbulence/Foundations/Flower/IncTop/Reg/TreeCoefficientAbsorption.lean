/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpectralMass
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootAmplitudeMass
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ExponentialCoefficientAbsorption

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeCoefficientAbsorption` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Exponential absorption of the tree root-partition coefficients -/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The spatial mask has no leaf-count dependence at spatial weight zero. -/
theorem maskedSourceSpatialConstant_zeroSpatial (d m J : ℕ) :
    maskedSourceSpatialConstantSpatial d m J 0 = maskedSourceFixedCoefficientSpatial d J 0 := by
  simp only [maskedSourceSpatialConstantSpatial, maskedSourceFixedCoefficientSpatial, pow_zero, mul_one]

/-- Fixed dimensional coefficient of the tree root partition. -/
@[expose] def treeSourceFixedCoefficientSpatial (d J : ℕ) : ℝ :=
  rootLocalOverlapConstantSpatial d * treeRootAmplitudeDerivativeFactorSpatial d J * maskedSourceFixedCoefficientSpatial d J 0

/-- Source-independent exponential constant for all actual tree spatial factors. -/
@[expose] def treeSourceExponentialCoefficientSpatial (d J K M : ℕ) (B C : ℝ) : ℝ :=
  max 1 (treeSourceFixedCoefficientSpatial d J) *
    (max 1 (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B)) ^ 3 *
      max 1 C * (max 1 (halfCellFourierConstant d)) ^ 2

theorem treeSourceExponentialCoefficient_posSpatial (d J K M : ℕ) (B C : ℝ) :
    0 < treeSourceExponentialCoefficientSpatial d J K M B C := by
  unfold treeSourceExponentialCoefficientSpatial
  positivity

/-- Literal extended-real tree coefficients are bounded exponentially in the source order. -/
theorem tree_source_ennreal_coefficient_leSpatial {d J K M n m : ℕ}
    (hn : 1 ≤ n) (hm : m + 1 ≤ 3 * n) {B C C₀ δ r : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    (ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
      (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
        ENNReal.ofReal (maskedSourceSpatialConstantSpatial d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))) *
      ENNReal.ofReal ((C₀ * δ) ^ n * r) ≤
        ENNReal.ofReal (((treeSourceExponentialCoefficientSpatial d J K M B C * C₀) * δ) ^ n * r) := by
  have ho : 0 ≤ rootLocalOverlapConstantSpatial d := by
    have hrad := treeRootCutoffRadius_nonnegSpatial d
    unfold rootLocalOverlapConstantSpatial
    positivity
  have ht := treeRootAmplitudeDerivativeFactor_nonnegSpatial d J
  have hfixed : 0 ≤ maskedSourceFixedCoefficientSpatial d J 0 := by
    rw [← maskedSourceSpatialConstant_zeroSpatial d 0 J]
    exact maskedSourceSpatialConstant_nonnegSpatial _ _ _ _
  have ha : 0 ≤ treeSourceFixedCoefficientSpatial d J := mul_nonneg (mul_nonneg ho ht) hfixed
  have hb : 0 ≤ leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg M))
    · exact zero_le_one.trans (le_max_left _ _)
  have hh := (halfCellFourierConstant_pos d).le
  have hcoef := order_coefficient_le_exponentialSpatial hn hm ha hb hC hh
  change _ ≤ treeSourceExponentialCoefficientSpatial d J K M B C ^ n at hcoef
  rw [maskedSourceSpatialConstant_zeroSpatial]
  have he : ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
      (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
        ENNReal.ofReal (maskedSourceFixedCoefficientSpatial d J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) =
      ENNReal.ofReal (treeSourceFixedCoefficientSpatial d J *
        (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) * C ^ n *
          halfCellFourierConstant d ^ (2 * n)) := by
    simp only [treeSourceFixedCoefficientSpatial, ENNReal.ofReal_mul ho,
      ENNReal.ofReal_mul (mul_nonneg ho ht), ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ho ht) hfixed),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg ho ht) hfixed) (pow_nonneg hb _)),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ho ht) hfixed) (pow_nonneg hb _)) (pow_nonneg hC _)),
      ENNReal.ofReal_pow hb, ENNReal.ofReal_pow hh]
    ring
  rw [he, ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg hb _)) (pow_nonneg hC _)) (pow_nonneg hh _))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ treeSourceExponentialCoefficientSpatial d J K M B C ^ n * ((C₀ * δ) ^ n * r) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg (mul_nonneg hC₀ hδ) _) hr)
    _ = _ := by simp only [mul_pow]; ring

end WaveTurbulence.Flower.IncTop