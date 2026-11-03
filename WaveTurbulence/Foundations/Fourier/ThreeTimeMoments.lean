/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DirectionalFourierMoments
import Mathlib.Tactic

/-!
# Joint decay in the two time frequencies and their sum

Eight square-free directional derivatives yield decay in `ξ₀`, `ξ₁`,
and `ξ₀ + ξ₁`. The diagonal derivative is applied first, so difference
phases remain constant before either boundary derivative is taken.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The eight derivative words for the two coordinate directions and the diagonal direction. -/
@[expose] def threeTimeMomentWords : List (List (Fin 2 → ℝ)) :=
  [[], [Pi.single 0 1], [Pi.single 1 1], [fun _ => 1],
    [Pi.single 0 1, Pi.single 1 1], [Pi.single 0 1, fun _ => 1],
    [Pi.single 1 1, fun _ => 1], [Pi.single 0 1, Pi.single 1 1, fun _ => 1]]

/-- The sum of the eight actual directional derivative `L¹` integrals. -/
@[expose] noncomputable def threeTimeMomentSum (f : (Fin 2 → ℝ) → ℂ) : ℝ :=
  (threeTimeMomentWords.map (fun w => ∫ x, ‖timeWordDerivative w f x‖)).sum

/-- Each derivative integral is bounded by the nonnegative sum containing it. -/
theorem integral_word_le_threeTimeMomentSum (f : (Fin 2 → ℝ) → ℂ)
    (w : List (Fin 2 → ℝ)) (hw : w ∈ threeTimeMomentWords) :
    (∫ x, ‖timeWordDerivative w f x‖) ≤ threeTimeMomentSum f := by
  apply List.single_le_sum ?_ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- Smooth compact functions have joint decay in both frequencies and their sum. -/
theorem norm_timeFourier_le_three_brackets {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ξ : Fin 2 → ℝ) :
    ‖timeFourier f ξ‖ ≤ 8 * threeTimeMomentSum f /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2) *
        Real.sqrt (1 + (ξ 0 + ξ 1) ^ 2)) := by
  have hm (w : List (Fin 2 → ℝ)) (hw : w ∈ threeTimeMomentWords) :
      (w.map (fun v => |timePairing 2 v ξ|)).prod * ‖timeFourier f ξ‖ ≤ threeTimeMomentSum f :=
    (timeFourier_word_moment_le_integral hf hc w ξ).trans
      (integral_word_le_threeTimeMomentSum f w hw)
  apply frequency_decay_three (timeFourier f ξ) (ξ 0) (ξ 1) (ξ 0 + ξ 1) (threeTimeMomentSum f)
  · simpa using hm [] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 0 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 1 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two] using
      hm [fun _ => 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 0 1, Pi.single 1 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 0 1, fun _ => 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 1 1, fun _ => 1] (by simp [threeTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply, mul_assoc] using
      hm [Pi.single 0 1, Pi.single 1 1, fun _ => 1] (by simp [threeTimeMomentWords])

end WaveTurbulence.Fourier
