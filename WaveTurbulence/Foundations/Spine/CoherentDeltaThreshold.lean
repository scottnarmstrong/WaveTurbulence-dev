/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentParameterSlack
/-! A single small-delta choice depends only on the already fixed low profile constant. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

private theorem exp_scaled_bound {x y : ℝ} (h : Real.exp 1 * x ≤ y) :
    x ≤ y * Real.exp (-1) := by
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  calc
    x = Real.exp (-1) * (Real.exp 1 * x) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (-1) * y := mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos _))
    _ = _ := mul_comm _ _

/-- The fixed high-order constants are absent from this smallness threshold. -/
theorem exists_coherent_delta_threshold {C : ℝ} (hC : 1 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) δ₀,
      δ ≤ 1 ∧
      64 * ((12 ^ 9 : ℕ) : ℝ) * C ^ 4 * δ ≤ Real.sqrt δ ∧
      (C + C ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * C ^ 2) * (2 * C ^ 2 * δ)) ≤
        Real.sqrt δ * Real.exp (-1) ∧
      C * δ ≤ Real.sqrt δ * Real.exp (-1) := by
  have hC0 : 0 < C := by linarith
  let B₁ : ℝ := 64 * ((12 ^ 9 : ℕ) : ℝ) * C ^ 4
  let B₂ : ℝ := Real.exp 1 * ((C + C ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * C ^ 2) * (2 * C ^ 2)))
  let B₃ : ℝ := Real.exp 1 * C
  obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_delta_sqrt_threshold (B := B₁) (by dsimp [B₁]; positivity)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_delta_sqrt_threshold (B := B₂) (by dsimp [B₂]; positivity)
  obtain ⟨δ₃, hδ₃, hb₃⟩ := exists_delta_sqrt_threshold (B := B₃) (by dsimp [B₃]; positivity)
  refine ⟨min δ₁ (min δ₂ δ₃), by positivity, ?_⟩
  intro δ hδ
  have h₁ := hb₁ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have h₂ := hb₂ δ ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have h₃ := hb₃ δ ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨h₁.1, h₁.2, ?_, ?_⟩
  · apply exp_scaled_bound
    convert h₂.2 using 1 <;> dsimp only [B₂] <;> ring
  · apply exp_scaled_bound
    simpa only [B₃, mul_assoc] using h₃.2

end WaveTurbulence.LGSpine
