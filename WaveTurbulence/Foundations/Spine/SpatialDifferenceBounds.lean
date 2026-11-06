/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NormAssembly
/-! Spatial subtraction and the final unit of large-L reserve in coherent comparisons. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem SNorm_sub_bound {d A B : ℕ} (hA : A ≠ 0) (f g : Mom d → ℂ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : SNorm A B f ≤ ENNReal.ofReal C) (hg : SNorm A B g ≤ ENNReal.ofReal D) :
    SNorm A B (fun k => f k - g k) ≤ ENNReal.ofReal (C + D) := by
  have hcf := contDiff_of_SNorm_bound hA f C hf
  have hcg := contDiff_of_SNorm_bound hA g D hg
  have hneg := SNorm_neg_bound g hcg D hD hg
  exact SNorm_add_bound f (-g) hcf hcg.neg C D hC hD hf hneg

theorem SNorm_sub_two_tails {d A B : ℕ} (hA : A ≠ 0) (f g : Mom d → ℂ)
    {δ L b : ℝ} (hδ : 0 ≤ δ) (hL : 2 ≤ L) (n : ℕ)
    (hf : SNorm A B f ≤ ENNReal.ofReal (δ ^ ((n : ℝ) / 2) * L ^ (-(b + 1))))
    (hg : SNorm A B g ≤ ENNReal.ofReal (δ ^ ((n : ℝ) / 2) * L ^ (-(b + 1)))) :
    SNorm A B (fun k => f k - g k) ≤ ENNReal.ofReal (δ ^ ((n : ℝ) / 2) * L ^ (-b)) := by
  have hL0 : 0 < L := by linarith
  have hnonneg : 0 ≤ δ ^ ((n : ℝ) / 2) * L ^ (-(b + 1)) := by positivity
  apply (SNorm_sub_bound hA f g hnonneg hnonneg hf hg).trans
  apply ENNReal.ofReal_le_ofReal
  have he : L * L ^ (-(b + 1)) = L ^ (-b) := by
    calc
      _ = L ^ (1 : ℝ) * L ^ (-(b + 1)) := by rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + -(b + 1)) := (Real.rpow_add hL0 _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = δ ^ ((n : ℝ) / 2) * (2 * L ^ (-(b + 1))) := by ring
    _ ≤ δ ^ ((n : ℝ) / 2) * (L * L ^ (-(b + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (by positivity)) (Real.rpow_nonneg hδ _)
    _ = _ := by rw [he]

end WaveTurbulence.LGSpine
