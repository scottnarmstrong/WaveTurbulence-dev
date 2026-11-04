/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourTimeMoments
import Mathlib.Tactic

/-!
# Two-bracket Fourier decay from endpoint moments

Only the four ordinary endpoint derivatives enter this estimate. In particular,
no diagonal derivative of an arbitrary input is charged in TARGET A.2.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The four square-free directional words for two time coordinates. -/
@[expose] def fourTimeMomentWords : List (List (Fin 2 → ℝ)) :=
  [[], [Pi.single 0 1], [Pi.single 1 1], [Pi.single 0 1, Pi.single 1 1]]

/-- The real-valued sum of the four actual derivative integrals. -/
@[expose] noncomputable def fourTimeMomentSum (f : (Fin 2 → ℝ) → ℂ) : ℝ :=
  (fourTimeMomentWords.map (fun w => ∫ x, ‖timeWordDerivative w f x‖)).sum

/-- Each endpoint moment is bounded by their sum. -/
theorem integral_word_le_fourTimeMomentSum (f : (Fin 2 → ℝ) → ℂ)
    (w : List (Fin 2 → ℝ)) (hw : w ∈ fourTimeMomentWords) :
    (∫ x, ‖timeWordDerivative w f x‖) ≤ fourTimeMomentSum f := by
  apply List.single_le_sum ?_ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- Smooth compact functions have two-bracket decay controlled by four moments. -/
theorem norm_timeFourier_le_two_brackets {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ξ : Fin 2 → ℝ) :
    ‖timeFourier f ξ‖ ≤ 4 * fourTimeMomentSum f /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2)) := by
  have hm (w : List (Fin 2 → ℝ)) (hw : w ∈ fourTimeMomentWords) :
      (w.map (fun v => |timePairing 2 v ξ|)).prod * ‖timeFourier f ξ‖ ≤ fourTimeMomentSum f :=
    (timeFourier_word_moment_le_integral hf hc w ξ).trans
      (integral_word_le_fourTimeMomentSum f w hw)
  apply frequency_decay_two (timeFourier f ξ) (ξ 0) (ξ 1) (fourTimeMomentSum f)
  · simpa using hm [] (by simp [fourTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 0 1] (by simp [fourTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 1 1] (by simp [fourTimeMomentWords])
  · simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using
      hm [Pi.single 0 1, Pi.single 1 1] (by simp [fourTimeMomentWords])

/-- The real and extended-real endpoint sums agree on smooth compact functions. -/
theorem ofReal_fourTimeMomentSum {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ENNReal.ofReal (fourTimeMomentSum f) = fourTimeMomentNorm f := by
  have hf1 := WaveTurbulence.contDiff_infty_partialDeriv hf 1
  have h0 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (0 : Fin 2)
  have h1 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (1 : Fin 2)
  have h01 : timeDirectionalDerivative (Pi.single 0 1)
      (timeDirectionalDerivative (Pi.single 1 1) f) =
      WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 f) := by
    rw [h1, timeDirectionalDerivative_single (hf1.differentiable (by simp))]
  have hi (w : List (Fin 2 → ℝ)) : Integrable (timeWordDerivative w f) := by
    obtain ⟨hw, hcw⟩ := timeWordDerivative_regular hf hc w
    exact hw.continuous.integrable_of_hasCompactSupport hcw
  have he (L : List (List (Fin 2 → ℝ))) :
      ENNReal.ofReal ((L.map (fun w => ∫ t, ‖timeWordDerivative w f t‖)).sum) =
      (L.map (fun w => ∫⁻ t, ‖timeWordDerivative w f t‖ₑ)).sum := by
    induction L with
    | nil => simp
    | cons w L ih =>
      have hn : 0 ≤ (L.map (fun w => ∫ t, ‖timeWordDerivative w f t‖)).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
        exact integral_nonneg (fun _ => norm_nonneg _)
      simp only [List.map_cons, List.sum_cons]
      rw [ENNReal.ofReal_add (integral_nonneg (fun _ => norm_nonneg _)) hn,
        ofReal_integral_norm_eq_lintegral_enorm (hi w), ih]
  unfold fourTimeMomentSum
  rw [he]
  simp only [fourTimeMomentWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    timeWordDerivative]
  rw [h01, h0, h1]
  simp only [fourTimeMomentNorm, fourTimeDerivatives, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]

end WaveTurbulence.Fourier
