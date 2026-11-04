/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.FactoredLinkMass

/-!
# Cancellation of lattice and coupling scales

TARGET (incohproof9), (incohproof16)–(incohproof18). The exact normalization
leaves `(C₀ δ/4)^n`, which is bounded by the stated `(C₀ δ)^n`.
-/

public section

namespace WaveTurbulence.Incoh

/-- The kinetic-scale cancellation is exact, including the source factor `2^(-2n)`. -/
theorem coupling_scale_identity {d n : ℕ} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ C : ℝ) :
    (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) * (C * kineticLinkScale d γ δ L) ^ n =
      (C * δ / 4) ^ n := by
  rw [pow_mul, ← mul_pow]
  congr 1
  unfold kineticLinkScale
  rw [show 2 * ((d : ℝ) - γ) = ((d : ℝ) - γ) * 2 by ring,
    Real.rpow_mul hL.le, Real.rpow_two]
  field_simp [hδ.ne', (Real.rpow_pos_of_pos hL ((d : ℝ) - γ)).ne']
  ring

/-- Discarding the harmless normalization factor gives the source's stated coupling scale. -/
theorem coupling_scale_le {d n : ℕ} {L δ C : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hC : 0 ≤ C) (γ : ℝ) :
    (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) * (C * kineticLinkScale d γ δ L) ^ n ≤
      (C * δ) ^ n := by
  rw [coupling_scale_identity hL hδ]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hC hδ.le]) n

end WaveTurbulence.Incoh
