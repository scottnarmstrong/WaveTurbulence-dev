/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Source decay exponent and kinetic-scale identities

TARGET standing notation L613 and (incohproof13)–(incohproof16).
-/

public section

namespace WaveTurbulence.Incoh

/-- The source's incoherence decay exponent `min(2γ,1,2(d−1)(1−γ))`. -/
@[expose] def incoherenceExponent (d : ℕ) (γ : ℝ) : ℝ :=
  min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

theorem incoherenceExponent_le_two_mul (d : ℕ) (γ : ℝ) :
    incoherenceExponent d γ ≤ 2 * γ := min_le_left _ _

theorem incoherenceExponent_le_one (d : ℕ) (γ : ℝ) :
    incoherenceExponent d γ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

theorem incoherenceExponent_le_longGain (d : ℕ) (γ : ℝ) :
    incoherenceExponent d γ ≤ 2 * ((d : ℝ) - 1) * (1 - γ) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem incoherenceExponent_pos {d : ℕ} (hd : 2 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) : 0 < incoherenceExponent d γ := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  unfold incoherenceExponent
  exact lt_min (mul_pos (by norm_num) hγ.1)
    (lt_min zero_lt_one (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hd')) (sub_pos.mpr hγ.2)))

/-- One inverse kinetic scale shifts the lattice exponent by `2γ`. -/
theorem inverse_scale_mul_rpow {L : ℝ} (hL : 0 < L) (δ γ C a : ℝ) :
    (δ * L ^ (2 * γ))⁻¹ * (C * L ^ a) = C * δ⁻¹ * L ^ (a - 2 * γ) := by
  rw [mul_inv_rev, ← Real.rpow_neg hL.le]
  calc
    _ = C * δ⁻¹ * (L ^ a * L ^ (-(2 * γ))) := by ring
    _ = _ := by rw [← Real.rpow_add hL, sub_eq_add_neg]

/-- The incoherent first moment shifts the lattice exponent by `4γ`. -/
theorem inverse_scale_sq_mul_rpow {L : ℝ} (hL : 0 < L) (δ γ C a : ℝ) :
    ((δ * L ^ (2 * γ))⁻¹) ^ 2 * (C * L ^ a) = C * (δ⁻¹) ^ 2 * L ^ (a - 4 * γ) := by
  calc
    _ = (δ * L ^ (2 * γ))⁻¹ * ((δ * L ^ (2 * γ))⁻¹ * (C * L ^ a)) := by ring
    _ = (δ * L ^ (2 * γ))⁻¹ * ((C * δ⁻¹) * L ^ (a - 2 * γ)) := by rw [inverse_scale_mul_rpow hL]
    _ = (C * δ⁻¹) * δ⁻¹ * L ^ ((a - 2 * γ) - 2 * γ) := inverse_scale_mul_rpow hL _ _ _ _
    _ = _ := by rw [show (a - 2 * γ) - 2 * γ = a - 4 * γ by ring]; ring

end WaveTurbulence.Incoh
