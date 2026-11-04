/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalizedAmplitude
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Lipschitz estimates for Fourier phases

A phase of frequency `η` has Lipschitz constant `|η|`. This frequency dependence
is used only in the small-energy error of DH21 Lemma 6.3(2); the main
principal-value estimate uses oscillatory cancellation instead.
-/

public section

open scoped NNReal

namespace WaveTurbulence.Resonant

/-- Exact frequency dependence of the unit phase's Lipschitz constant. -/
theorem lipschitzWith_unitPhase (η : ℝ) :
    LipschitzWith ⟨|η|, abs_nonneg η⟩ (unitPhase η) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : unitPhase η x - unitPhase η y = unitPhase η y * (unitPhase η (x - y) - 1) := by
    have h := unitPhase_add η y (x - y)
    have he : y + (x - y) = x := by ring
    rw [he] at h
    rw [h]
    ring
  rw [he, norm_mul, norm_unitPhase, one_mul]
  have hn : ‖unitPhase η (x - y) - 1‖ ≤ |η * (x - y)| := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := η * (x - y))
    rw [mul_comm Complex.I ((η * (x - y) : ℝ) : ℂ)] at h
    simpa only [unitPhase, Real.norm_eq_abs] using h
  exact hn.trans_eq (by rw [abs_mul, ← Real.dist_eq]; rfl)

/-- Product with a Fourier phase: the derivative cost is linear in frequency. -/
theorem lipschitzWith_mul_unitPhase {f : ℝ → ℂ} {K B : ℝ≥0}
    (hL : LipschitzWith K f) (hb : ∀ u, ‖f u‖ ≤ B) (η : ℝ) :
    LipschitzWith (K + B * ⟨|η|, abs_nonneg η⟩) (fun u => f u * unitPhase η u) := by
  have h := lipschitzWith_mul_of_bounds (Bg := 1) hL (lipschitzWith_unitPhase η) hb
    (fun u => (norm_unitPhase η u).le)
  simpa only [mul_one, add_comm] using h

end WaveTurbulence.Resonant
