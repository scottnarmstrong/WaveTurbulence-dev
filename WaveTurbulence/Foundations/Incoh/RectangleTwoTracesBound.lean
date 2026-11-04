/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.UniversalRectangleApprox
public import WaveTurbulence.Foundations.Incoh.MixedTimeTraceTwice
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform two-endpoint bounds for literal fourfold rectangular kernels

TARGET's fixed-integer endpoint variants of (incohproof23). Neither the
frozen clock nor the six phase/interval parameters need regularity in the
external vector parameter.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Incoh

/-- Both external endpoints of a hard rectangular fourfold kernel may be frozen. -/
theorem exists_rectangleV_twoTraces_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ V : Type*,
      ∀ p : V → Mom 6, ∀ c₀ c₁ : V → ℝ, ∀ j₀ j₁ : Fin 2,
      Fourier.mixedFourierNorm00 (1 / 4) (fun t v =>
        cutoffTimeTrace χ j₁ (c₁ v)
          (cutoffTimeTrace χ j₀ (c₀ v) (fun u => universalRectangleV χ u (p v))) t) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hCb⟩ := exists_smoothUniversalRectangleV_bound hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  let T := ENNReal.ofReal (2 ^ ((1 : ℝ) / 4)) *
    Fourier.timeFourierNorm (1 / 4) (Fourier.coordinateCutoff (r := 2) χ)
  let K := T * (T * ENNReal.ofReal C)
  have hT : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (Fourier.timeFourierNorm_lt_top_of_smooth_compact (1 / 4)
      (Fourier.coordinateCutoff_hasCompactSupport hcχ) (Fourier.coordinateCutoff_contDiff hχ)).ne
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top hT (ENNReal.mul_ne_top hT ENNReal.ofReal_ne_top)
  have hKC : K ≤ ENNReal.ofReal (1 + K.toReal) := by
    calc
      _ = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨1 + K.toReal, by positivity, ?_⟩
  intro V p c₀ c₁ j₀ j₁
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hn (n : ℕ) : Fourier.mixedFourierNorm00 (1 / 4)
      (fun t v => smoothUniversalRectangleV χ (ε n) t (p v)) ≤ ENNReal.ofReal C :=
    (mixedFourierNorm00_comp_le (1 / 4) (smoothUniversalRectangleV χ (ε n)) p).trans
      (hCb (ε n) (hε n))
  apply le_trans _ hKC
  exact mixedFourierNorm00_cutoffTimeTrace_twice_limit_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hχ hcχ
    (fun n v => contDiff_smoothUniversalRectangleV hχ (ε n) (p v))
    (fun n v => hasCompactSupport_smoothUniversalRectangleV h (ε n) (p v))
    (fun n v t => norm_smoothUniversalRectangleV_le h (hε n) (p v) t)
    (fun v t => tendsto_smoothUniversalRectangleV hχ h hε hlim (p v) t) hn j₀ j₁ c₀ c₁

end WaveTurbulence.Incoh
