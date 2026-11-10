/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.ThreeTimeMoments
import Mathlib.Tactic

/-!
# The four endpoint moments and their diagonal counterparts

The eight moments used in the quarter-order estimate consist exactly of
the four ordinary endpoint moments of the output and of its diagonal derivative.
All derivatives are the frozen coordinate partials.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The function and its three square-free endpoint derivatives. -/
@[expose] noncomputable def fourTimeDerivatives (f : (Fin 2 → ℝ) → ℂ) :
    Fin 4 → ((Fin 2 → ℝ) → ℂ) :=
  ![f, WaveTurbulence.partialDeriv 0 f, WaveTurbulence.partialDeriv 1 f,
    WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 f)]

/-- The sum of the actual four endpoint derivative `L¹` integrals. -/
@[expose] noncomputable def fourTimeMomentNorm (f : (Fin 2 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ j : Fin 4, ∫⁻ t, ‖fourTimeDerivatives f j t‖ₑ

private theorem ofReal_word_integral_sum {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (L : List (List (Fin 2 → ℝ))) :
    ENNReal.ofReal ((L.map (fun w => ∫ t, ‖timeWordDerivative w f t‖)).sum) =
      (L.map (fun w => ∫⁻ t, ‖timeWordDerivative w f t‖ₑ)).sum := by
  induction L with
  | nil => simp
  | cons w L ih =>
    obtain ⟨hw, hcw⟩ := timeWordDerivative_regular hf hc w
    have hi : Integrable (timeWordDerivative w f) := hw.continuous.integrable_of_hasCompactSupport hcw
    have ht : 0 ≤ (L.map (fun w => ∫ t, ‖timeWordDerivative w f t‖)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact integral_nonneg (fun _ => norm_nonneg _)
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (integral_nonneg (fun _ => norm_nonneg _)) ht,
      ofReal_integral_norm_eq_lintegral_enorm hi, ih]

/-- The actual eight-moment sum equals the four moments of the output plus those of its diagonal derivative. -/
theorem ofReal_threeTimeMomentSum_eq_four {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ENNReal.ofReal (threeTimeMomentSum f) = fourTimeMomentNorm f +
      fourTimeMomentNorm (timeDirectionalDerivative (fun _ => 1) f) := by
  let g := timeDirectionalDerivative (fun _ => 1) f
  have hg : ContDiff ℝ ∞ g := timeDirectionalDerivative_contDiff hf _
  have hf1 := WaveTurbulence.contDiff_infty_partialDeriv hf 1
  have hg1 := WaveTurbulence.contDiff_infty_partialDeriv hg 1
  have h0 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (0 : Fin 2)
  have h1 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (1 : Fin 2)
  have h01 : timeDirectionalDerivative (Pi.single 0 1)
      (timeDirectionalDerivative (Pi.single 1 1) f) =
      WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 f) := by
    rw [h1, timeDirectionalDerivative_single (hf1.differentiable (by simp))]
  have h0g := timeDirectionalDerivative_single (hg.differentiable (by simp)) (0 : Fin 2)
  have h1g := timeDirectionalDerivative_single (hg.differentiable (by simp)) (1 : Fin 2)
  have h01g : timeDirectionalDerivative (Pi.single 0 1)
      (timeDirectionalDerivative (Pi.single 1 1) g) =
      WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 g) := by
    rw [h1g, timeDirectionalDerivative_single (hg1.differentiable (by simp))]
  unfold threeTimeMomentSum
  rw [ofReal_word_integral_sum hf hc]
  simp only [threeTimeMomentWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    timeWordDerivative]
  rw [h01, h01g, h0, h1, h0g, h1g]
  simp only [fourTimeMomentNorm, fourTimeDerivatives, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  ring

end WaveTurbulence.Fourier
