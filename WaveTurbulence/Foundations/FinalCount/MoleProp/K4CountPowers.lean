/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact exponent margins in the K4 terminal count

The elementary small-radius branch leaves a 1.05 γ₀ saving and the
large-radius annulus branch leaves 1.1 γ₀ before logarithmic losses.
The required source saving is 1.01 γ₀.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- The shell's low/high-γ planar dimension factor has a uniform exact form. -/
theorem k4_planar_exponent_identity (γ : ℝ) :
    max 1 (2-2*γ) = 2-γ-min γ (1-γ) := by
  by_cases h : γ ≤ 1/2
  · rw [min_eq_left (by linarith only [h]),max_eq_right (by linarith only [h])]
    ring
  · rw [min_eq_right (by linarith only [h]),max_eq_left (by linarith only [h])]
    ring

/-- All three terms of the actual large-radius annulus majorant fit with
one tenth γ₀ of extra planar saving. -/
theorem k4_large_radius_exponents {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    1-γ ≤ max 1 (2-2*γ)-min γ (1-γ)/10 ∧
    2-3*γ+min γ (1-γ)/10 ≤ max 1 (2-2*γ)-min γ (1-γ)/10 ∧
    (4 : ℝ)/3-γ+min γ (1-γ)/30 ≤ max 1 (2-2*γ)-min γ (1-γ)/10 := by
  rw [k4_planar_exponent_identity]
  by_cases h : γ ≤ 1/2
  · rw [min_eq_left (by linarith only [h])]
    constructor
    · linarith only [hγ,h]
    constructor <;> linarith only [hγ,h]
  · rw [min_eq_right (by linarith only [h])]
    constructor
    · linarith only [hγ1,h]
    constructor <;> linarith only [hγ1,h]

/-- Base-triple and complementary-coordinate powers combine with the
large-radius planar saving to leave exactly 1.1 γ₀. -/
theorem k4_large_total_exponent (d γ : ℝ) :
    2*(d-γ)+(d-2)+(max 1 (2-2*γ)-min γ (1-γ)/10) =
      3*(d-γ)-(11 : ℝ)/10*min γ (1-γ) := by
  rw [k4_planar_exponent_identity]
  ring

/-- Every fixed-coefficient exceptional fiber has enough power saving
already from its literal two-free-label box count. -/
theorem k4_exception_exponent_le {d γ : ℝ} (hd : 3 ≤ d) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    2*d ≤ 3*(d-γ)-(101 : ℝ)/100*min γ (1-γ) := by
  by_cases h : γ ≤ 1/2
  · rw [min_eq_left (by linarith only [h])]
    linarith only [hd,hγ,h]
  · rw [min_eq_right (by linarith only [h])]
    linarith only [hd,hγ1,h]

end WaveTurbulence.MoleProp
