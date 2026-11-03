/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeIntegralFiniteInputs
import Mathlib.Tactic

/-!
# TARGET Lemma A.2 in the existing time Fourier norms

Both literal operators act on arbitrary complex-valued inputs. An infinite
input norm makes the estimate immediate; finite input norms supply all
measurability and integrability needed by the approximation argument.
The small-parameter range is explicitly `0 < η ≤ 1/3`. Constants depend
only on `χ` and `η`, and are uniform in momentum dimension.

The rectangular proof replaces TARGET L2370's missing logarithm by
physical endpoint `Lᵖ` bounds, norm-one Hausdorff–Young, and Hölder with a
strictly integrable multiplier. The order-zero mixed norm uses the owner's
ruling: time integrability is retained and momentum continuity is omitted.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- TARGET A.2, with a positive cutoff-dependent constant and no extra regularity assumptions on `F`. -/
theorem exists_cutoff_timeIntegral_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 3)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ F : (Fin 2 → ℝ) → ℂ,
        timeFourierNorm η (cutoffDoubleIntegral χ F) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal (1 + 3 * η))) ∧
      (∀ (d : ℕ) (F : (Fin 2 → ℝ) → Mom d → ℂ),
        mixedFourierNorm (-η) 0 0 (cutoffJ χ F) ≤ ENNReal.ofReal C * uniformTimeL1 F) := by
  obtain ⟨h⟩ := exists_cutoffControl hχ hcχ
  let KR := rectangleTimeFactor η h.radius h.bound
  let KT := ENNReal.ofReal (4 * negativeFrequencyConstant η) *
    orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)
  have hKR : KR ≠ ⊤ := rectangleTimeFactor_ne_top hη hη1 _ _
  have hKT : KT ≠ ⊤ := by
    have hm := orderedFourMomentFactor_ne_top h.radius h.bound
    dsimp [KT]
    finiteness
  let K := max KR KT
  have hK : K ≠ ⊤ := (max_lt hKR.lt_top hKT.lt_top).ne
  let C : ℝ := 1 + K.toReal
  have hC : 0 < C := by dsimp [C]; linarith [ENNReal.toReal_nonneg (a := K)]
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      _ = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_, ?_⟩
  · intro F
    by_cases hf : eLpNorm F (ENNReal.ofReal (1 + 3 * η)) = ⊤
    · rw [hf, ENNReal.mul_top hC0]
      exact le_top
    · have hm : MemLp F (ENNReal.ofReal (1 + 3 * η)) := lt_top_iff_ne_top.mpr hf
      exact (timeFourierNorm_cutoffDoubleIntegral_memLp_le hη hη1 hχ h hm).trans
        (mul_le_mul' ((le_max_left KR KT).trans hKC) le_rfl)
  · intro d F
    by_cases hf : uniformTimeL1 F = ⊤
    · rw [hf, ENNReal.mul_top hC0]
      exact le_top
    · have hMt : uniformTimeL1 F < ⊤ := lt_top_iff_ne_top.mpr hf
      have hm (k : Mom d) : MemLp (fun t => F t k) 1 := by
        have hs : eLpNorm (fun t => F t k) 1 volume ≤ uniformTimeL1 F :=
          le_iSup (fun k => eLpNorm (fun t => F t k) 1 volume) k
        exact hs.trans_lt hMt
      exact (mixedFourierNorm_cutoffJ_memLp_le hη hχ hcχ h hm).trans
        (mul_le_mul' ((le_max_right KR KT).trans hKC) le_rfl)

end WaveTurbulence.Fourier
