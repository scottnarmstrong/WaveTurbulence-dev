/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Arith96
import Mathlib.Tactic

/-! # Prop 9.6: interpolation between two bounds (DH23 L1855, "interpolate (roughbd) with ...") -/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8

/-- `min(x₁, x₂) ≤ x₁^θ x₂^{1-θ}`: the interpolation of two bounds. -/
theorem interp_le {A : ℝ≥0∞} {x1 x2 θ : ℝ} (h1 : A ≤ ENNReal.ofReal x1) (h2 : A ≤ ENNReal.ofReal x2)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    A ≤ ENNReal.ofReal (x1 ^ θ * x2 ^ (1 - θ)) := by
  rcases le_total x1 x2 with h | h
  · refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    calc x1 = x1 ^ θ * x1 ^ (1 - θ) := by
          rw [← Real.rpow_add' hx1 (by linarith)]; simp
      _ ≤ x1 ^ θ * x2 ^ (1 - θ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx1 h (by linarith)) (Real.rpow_nonneg hx1 _)
  · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc x2 = x2 ^ θ * x2 ^ (1 - θ) := by
          rw [← Real.rpow_add' hx2 (by linarith)]; simp
      _ ≤ x1 ^ θ * x2 ^ (1 - θ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx2 h hθ0) (Real.rpow_nonneg hx2 _)

/-- Interpolation of `L^{a}` and `L^{b}`. -/
theorem interp_L {A : ℝ≥0∞} {L a b θ : ℝ} (hL : 1 ≤ L) (h1 : A ≤ ENNReal.ofReal (L ^ a))
    (h2 : A ≤ ENNReal.ofReal (L ^ b)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    A ≤ ENNReal.ofReal (L ^ (θ * a + (1 - θ) * b)) := by
  have hL0 : 0 < L := by linarith
  have := interp_le h1 h2 (Real.rpow_nonneg hL0.le a) (Real.rpow_nonneg hL0.le b) hθ0 hθ1
  rwa [← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, mul_comm a θ, mul_comm b (1 - θ)] at this


/-- **The endgame**: `𝔄 ≤ L^{E₁}` (roughbd) and `𝔄 ≤ f L^{b}` with `f ≥ 1` give `𝔄 ≤ f L^{e}` as soon as
`θ E₁ + (1-θ) b ≤ e`. -/
theorem endgame {A : ℝ≥0∞} {L f E1 b e θ : ℝ} (hL : 1 ≤ L) (hf : 1 ≤ f) (h1 : A ≤ ENNReal.ofReal (L ^ E1))
    (h2 : A ≤ ENNReal.ofReal (f * L ^ b)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he : θ * E1 + (1 - θ) * b ≤ e) :
    A ≤ ENNReal.ofReal (f * L ^ e) := by
  have hL0 : 0 < L := by linarith
  have hf0 : 0 < f := by linarith
  have := interp_le h1 h2 (Real.rpow_nonneg hL0.le E1) (mul_nonneg hf0.le (Real.rpow_nonneg hL0.le b)) hθ0 hθ1
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.mul_rpow hf0.le (Real.rpow_nonneg hL0.le b), ← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le]
  have hf1 : f ^ (1 - θ) ≤ f := by
    calc f ^ (1 - θ) ≤ f ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hf (by linarith)
      _ = f := Real.rpow_one f
  have hexp : L ^ (E1 * θ) * (f ^ (1 - θ) * L ^ (b * (1 - θ))) = f ^ (1 - θ) * L ^ (θ * E1 + (1 - θ) * b) := by
    rw [mul_left_comm, ← Real.rpow_add hL0]; ring_nf
  rw [hexp]
  calc f ^ (1 - θ) * L ^ (θ * E1 + (1 - θ) * b) ≤ f * L ^ e :=
      mul_le_mul hf1 (Real.rpow_le_rpow_of_exponent_le hL he) (Real.rpow_nonneg hL0.le _) hf0.le

end WaveTurbulence.FinalCountG8
