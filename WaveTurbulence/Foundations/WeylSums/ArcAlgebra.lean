/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ArcProfile
import Mathlib.Tactic

/-!
# Real-power comparison with rational-arc profiles

The square of `1+L sqrt β` dominates `1+L²β`. This elementary comparison
turns the log-free Gauss bound into an integrable rational-arc envelope.
-/

public section

namespace WaveTurbulence.WeylSums

/-- Polynomial core of the arc-profile comparison. -/
theorem square_majorArc_bound (X A L P B : ℝ)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hL : 0 ≤ L) (hP : 0 < P) (hB : 0 ≤ B)
    (hbound : X * (P * (1 + L * B)) ≤ A) :
    X ^ 2 * P ^ 2 * (1 + L ^ 2 * B ^ 2) ≤ A ^ 2 := by
  have h0 : 0 ≤ X * (P * (1 + L * B)) := by positivity
  have hs := (sq_le_sq₀ h0 hA).mpr hbound
  have hLB := mul_nonneg hL hB
  have hw : 1 + L ^ 2 * B ^ 2 ≤ (1 + L * B) ^ 2 := by nlinarith only [hLB]
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg X) (sq_nonneg P))
  nlinarith only [hs, hm]

/-- A real-power form of the Gauss bound, ready for integration over arcs. -/
theorem rpow_le_scaledArcProfile (X A L Q β p : ℝ)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hL : 0 ≤ L) (hQ : 0 < Q) (hβ : 0 ≤ β) (hp : 0 ≤ p)
    (hbound : X ≤ A / (Real.sqrt Q * (1 + L * Real.sqrt β))) :
    X ^ p ≤ A ^ p * Q ^ (-p / 2) * arcProfile (p / 2) (L ^ 2 * β) := by
  have hden : 0 < Real.sqrt Q * (1 + L * Real.sqrt β) :=
    mul_pos (Real.sqrt_pos.mpr hQ) (by positivity)
  have hs := square_majorArc_bound X A L (Real.sqrt Q) (Real.sqrt β)
    hX hA hL (Real.sqrt_pos.mpr hQ) (Real.sqrt_nonneg _) ((le_div_iff₀ hden).mp hbound)
  rw [Real.sq_sqrt hQ.le, Real.sq_sqrt hβ] at hs
  have hden' : 0 < Q * (1 + L ^ 2 * β) := by positivity
  have hs' : X ^ 2 ≤ A ^ 2 / (Q * (1 + L ^ 2 * β)) := by
    apply (le_div_iff₀ hden').mpr
    simpa only [mul_assoc] using hs
  have hp2 : 0 ≤ p / 2 := div_nonneg hp (by norm_num)
  have hXp : X ^ p = (X ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX]
    congr 1
    ring
  have hAp : (A ^ 2) ^ (p / 2) = A ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul hA]
    congr 1
    ring
  calc
    _ = (X ^ 2) ^ (p / 2) := hXp
    _ ≤ (A ^ 2 / (Q * (1 + L ^ 2 * β))) ^ (p / 2) :=
      Real.rpow_le_rpow (sq_nonneg X) hs' hp2
    _ = _ := by
      rw [Real.div_rpow (sq_nonneg A) hden'.le, hAp,
        Real.mul_rpow hQ.le (by positivity)]
      simp only [arcProfile, abs_of_nonneg (mul_nonneg (sq_nonneg L) hβ),
        show (-p / 2 : ℝ) = -(p / 2) by ring, Real.rpow_neg hQ.le, Real.rpow_neg (by positivity : 0 ≤ 1 + L ^ 2 * β),
        div_eq_mul_inv, mul_inv]
      ring

end WaveTurbulence.WeylSums
