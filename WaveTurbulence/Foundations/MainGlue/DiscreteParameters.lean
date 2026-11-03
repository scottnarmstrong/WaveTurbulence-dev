/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# G10(a,b): integer induction length and probability exponent

The elementary parameter choices from SEAL-PLAN §B.4. The statements use
ordinary scalar parameters and do not depend on the unfrozen Wave B records.
-/

public section

namespace WaveTurbulence.MainGlue

/-- G10(b): ceiling subdivision preserves positive time and the upper step bound. -/
theorem ceiling_subdivision {τ δ₀ : ℝ} (hτ : 0 < τ) (hδ₀ : 0 < δ₀) :
    let D : ℕ := ⌈τ / δ₀⌉₊
    let δ : ℝ := τ / D
    1 ≤ D ∧ 0 < δ ∧ δ ≤ δ₀ ∧ τ = D * δ := by
  dsimp only
  have hD : 0 < ⌈τ / δ₀⌉₊ := Nat.ceil_pos.mpr (div_pos hτ hδ₀)
  have hDreal : 0 < (⌈τ / δ₀⌉₊ : ℝ) := Nat.cast_pos.mpr hD
  refine ⟨hD, div_pos hτ hDreal, ?_, ?_⟩
  · apply (div_le_iff₀ hDreal).mpr
    have h := (div_le_iff₀ hδ₀).mp (Nat.le_ceil (τ / δ₀))
    nlinarith only [h]
  · field_simp

/-- A floor loses at most a factor two above two. -/
theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith only [hx, h]

/-- G10(a), numerical core: a floor followed by a sufficiently large power exceeds its input. -/
theorem le_nat_floor_pow {x : ℝ} (hx : 4 ≤ x) {N : ℕ} (hN : 2 ≤ N) :
    x ≤ (⌊x⌋₊ : ℝ) ^ N := by
  have hf := half_le_nat_floor (show 2 ≤ x by linarith only [hx])
  have hf2 : 2 ≤ (⌊x⌋₊ : ℝ) := by linarith only [hx, hf]
  have hs : x ≤ (⌊x⌋₊ : ℝ) ^ 2 := by
    nlinarith only [hf, hf2, mul_nonneg (Nat.cast_nonneg ⌊x⌋₊) (sub_nonneg.mpr hf2)]
  exact hs.trans (pow_le_pow_right₀ (by linarith only [hf2]) hN)

/-- G10(a): the final probability exponent dominates the one in frozen Theorem 1.1. -/
theorem log_pow_le_final_exponent {d : ℕ} (hd : 1 ≤ d) {L : ℝ}
    (hlog : 4 ≤ Real.log L ^ (40 * d)) :
    Real.log L ^ (40 * d) ≤ (⌊Real.log L ^ (40 * d)⌋₊ : ℝ) ^ (40 * d) :=
  le_nat_floor_pow hlog (by omega)

end WaveTurbulence.MainGlue
