/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxKernel
public import WaveTurbulence.Foundations.Incoh.LocalizedIntervalBound
public import WaveTurbulence.Foundations.Incoh.InvariantOrderedNorm

/-!
# Uniform quarter regularity with every selected time-box bound retained

TARGET (incohproof28), including the integer-endpoint cases. The constant
depends only on the cutoff and the number of selected clocks (two or four),
not on phases, interval endpoints, or smoothing width.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Literal smooth causal box kernels have a common quarter-regularity bound. -/
theorem exists_smoothCausalBoxKernel_bound (m : ℕ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ V : Type*,
      ∀ phase a b : V → Fin (m + 2) → ℝ,
      (∀ k, ∑ j, phase k j = 0) → (∀ k, a k ≤ b k) → ∀ ε : ℝ, 0 < ε →
      Fourier.mixedFourierNorm00 (1 / 4) (fun t k => smoothCausalBoxKernel m χ ε (phase k) (a k) (b k) t) ≤
        ENNReal.ofReal C := by
  obtain ⟨B, hB, hBm⟩ := exists_localizedInterval_firstVariation_bound hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  let Q := ENNReal.ofReal (8 * Fourier.jointFrequencyConstant) *
    (Fourier.orderedFourMomentFactor h.radius h.bound *
      ((3 + (m + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ (m + 2)))
  have hQ : Q ≠ ⊤ := by
    have ho := Fourier.orderedFourMomentFactor_ne_top h.radius h.bound
    dsimp only [Q]
    finiteness
  have hQC : Q ≤ ENNReal.ofReal (1 + Q.toReal) := by
    calc
      _ = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQ).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨1 + Q.toReal, by positivity, ?_⟩
  intro V phase a b hp hab ε hε
  apply le_trans ?_ hQC
  exact mixedFourierNorm00_invariantOrdered_le hχ h
    (fun k j => localizedInterval χ ε (a k j) (b k j))
    (fun k j => contDiff_localizedInterval hχ ε (a k j) (b k j)) phase hp
    (fun _ => smoothOrderingWeight (m + 1) ε) (fun _ => contDiff_smoothOrderingWeight (m + 1) ε)
    (fun _ => norm_smoothOrderingWeight_le (m + 1) ε)
    (fun _ => smoothOrderingWeight_translate (m + 1) ε)
    (B := ENNReal.ofReal B)
    (fun k j => setLIntegral_norm_localizedInterval_le hχ hcχ
      (hBm ε (a k j) (b k j) hε (hab k j)).1 h.radius)
    (fun k j => setLIntegral_norm_deriv_localizedInterval_le hχ hcχ
      (hBm ε (a k j) (b k j) hε (hab k j)).2 h.radius)

end WaveTurbulence.Incoh
