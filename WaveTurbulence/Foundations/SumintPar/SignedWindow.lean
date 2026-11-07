/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Reflected closed time windows (SUMINT-SIGNED)

A time rescaling by a sign `ε = ±1` reflects the closed window about the centre `t`. The reflected
window has the same size constraints, so every window estimate holds for either sign.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Reflection of a closed interval about a point. -/
theorem integral_Icc_comp_reflect (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (∫ s in Icc a b, g (2*t - s)) = ∫ s in Icc (2*t-b) (2*t-a), g s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_left g (2*t),
    intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-- A signed affine time window is an unsigned one, with a reflected window of the same size
constraints. -/
theorem integral_Icc_signed_window {c t B a b ε : ℝ} (h : ε = 1 ∨ ε = -1)
    (hab : a ≤ b) :
    ∃ a' b' : ℝ, a' ≤ b' ∧
      (-B ≤ c*(a-t) → c*(b-t) ≤ B → -B ≤ c*(a'-t) ∧ c*(b'-t) ≤ B) ∧
      ∀ G : ℝ → ℝ, (∫ s in Icc a b, G (ε*(c*(s-t)))) = ∫ s in Icc a' b', G (c*(s-t)) := by
  rcases h with rfl | rfl
  · exact ⟨a, b, hab, fun h1 h2 => ⟨h1, h2⟩, fun G => by simp only [one_mul]⟩
  · refine ⟨2*t-b, 2*t-a, by linarith, fun h1 h2 => ⟨by nlinarith, by nlinarith⟩, fun G => ?_⟩
    have := integral_Icc_comp_reflect (fun x => G (c*(x-t))) hab t
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    congr 1
    ring

end WaveTurbulence.SumintPar
