/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MixedInterpolation
public import WaveTurbulence.Foundations.Incoh.InterpolationExponents

/-!
# Interpolating two estimates of one literal tree extension

This conditional norm inequality is used only after both endpoint bounds
have been proved for the globally identified source extension.
-/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional interpolation: a two-link quarter-norm loss costs at most `16dη`. -/
theorem mixedFourierNorm00_le_of_tree_endpoints {r d : ℕ} {V : Type*}
    {η L : ℝ} (hη : 0 < η) (hη₁ : η < 1 / 4) (hL : 1 ≤ L)
    (F : (Fin r → ℝ) → V → ℂ) (M : ℝ≥0∞)
    (hneg : Fourier.mixedFourierNorm00 (-η) F ≤ M)
    (hpos : Fourier.mixedFourierNorm00 (1 / 4) F ≤ M * ENNReal.ofReal (L ^ ((d : ℝ) * 2))) :
    Fourier.mixedFourierNorm00 η F ≤ M * ENNReal.ofReal (L ^ (16 * (d : ℝ) * η)) := by
  let a := treeInterpolationWeight η
  have ha : 0 < a := treeInterpolationWeight_pos hη
  have ha₁ : a < 1 := treeInterpolationWeight_lt_one hη.le hη₁
  have hb : 0 ≤ 1 - a := (sub_pos.mpr ha₁).le
  have he := mixedFourierNorm00_interpolate (1 / 4) (-η) ha ha₁ F
  rw [treeInterpolationWeight_identity hη.le] at he
  apply he.trans
  calc
    _ ≤ (M * ENNReal.ofReal (L ^ ((d : ℝ) * 2))) ^ a * M ^ (1 - a) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hpos ha.le) (ENNReal.rpow_le_rpow hneg hb)
    _ = (M ^ a * M ^ (1 - a)) * ENNReal.ofReal (L ^ ((d : ℝ) * 2)) ^ a := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le]
      ac_rfl
    _ = M * ENNReal.ofReal (L ^ (((d : ℝ) * 2) * a)) := by
      rw [← ENNReal.rpow_add_of_nonneg a (1 - a) ha.le hb,
        add_sub_cancel, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) _) ha.le,
        ← Real.rpow_mul (zero_le_one.trans hL)]
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le hL
      have h := mul_le_mul_of_nonneg_left (treeInterpolationWeight_le_eight_mul hη.le)
        (show 0 ≤ (d : ℝ) * 2 by positivity)
      dsimp only [a]
      nlinarith only [h]

end WaveTurbulence.Incoh
