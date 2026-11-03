/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exponent bookkeeping for the minor-arc integral -/

public section
namespace WaveTurbulence.WeylSums

/-- The denominator loss can be chosen below both the summability margin
and the requested power loss. -/
theorem exists_minor_arc_loss (d : ℕ) (hd : 3 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < (d : ℝ)-2 ∧ 2*ε ≤ η := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨min (η/4) (((d : ℝ)-2)/2), lt_min (by positivity) (by linarith only [hdR]), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by linarith only [hdR])
  · have hh := min_le_left (η/4) (((d : ℝ)-2)/2)
    linarith only [hh,hη]

/-- The refined window exponent gives the exact power in TARGET Lemma 5.3. -/
theorem bilinear_minor_exponent_le (d γ ε η : ℝ) (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε) (hεη : 2*ε ≤ η) :
    2*d+(2*γ-2)*(d-1-ε) ≤ 2*d-2*(d-1)*(1-γ)+η := by
  have hh : 0 ≤ ε*γ := mul_nonneg hε hγ
  nlinarith only [hh,hεη]

/-- Normalizing the upper physical time scale. -/
theorem upper_time_window_power {L : ℝ} (hL : 0 < L) (T₀ γ : ℝ) :
    T₀*L^(2*γ)/(4*L^2) = (T₀/4)*L^(2*γ-2) := by
  rw [Real.rpow_sub hL, Real.rpow_two]
  field_simp [hL.ne']

/-- Combining the lattice and time-window powers. -/
theorem bilinear_minor_scale_identity {L T₀ : ℝ} (hL : 0 < L) (hT₀ : 0 ≤ T₀)
    (d γ ε : ℝ) :
    L^(2*d)*(T₀*L^(2*γ)/(4*L^2))^(d-1-ε) =
      (T₀/4)^(d-1-ε) * L^(2*d+(2*γ-2)*(d-1-ε)) := by
  rw [upper_time_window_power hL, Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
    ← Real.rpow_mul hL.le, Real.rpow_add hL]
  ring

end WaveTurbulence.WeylSums
