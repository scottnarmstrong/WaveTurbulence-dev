/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.Estcross

/-! # A codimension-two form of the proved estcross estimate -/

public section
namespace WaveTurbulence.CountLemmas

/-- Under the source scale `ρ≤L`, the small-vector term in estcross is
absorbed into its codimension-two term. No lower bound on |x| is assumed. -/
theorem card_dense_strips_codim_two_le {d : ℕ}
    (s : Finset (Fin (d+3) → ℤ)) (c : Fin (d+3) → ℝ)
    {ρ θ L : ℝ} (hL : 1 ≤ L) (hρ : 0 ≤ ρ) (hθ : 1 ≤ θ)
    (hscale : 16*((3 : ℝ)^(d+1)*θ) ≤ ρ) (hρL : ρ ≤ L)
    (hbox : ∀ x ∈ s, ∀ i, |(x i : ℝ)-c i| ≤ L)
    (hdense : ∀ x ∈ s,
      ∃ Y : Finset (Fin (d+3) → ℤ), ∃ b : Fin (d+3) → ℝ, ∃ α : ℝ,
        (∀ y ∈ Y, ∀ i, |(y i : ℝ)-b i| ≤ L) ∧
        (∀ y ∈ Y, |(∑ i, (x i : ℝ)*(y i : ℝ))-α| ≤ ρ) ∧
        L^(d+2)/θ ≤ (Y.card : ℝ)) :
    (s.card : ℝ) ≤ 2*((5 : ℝ)^(d+3)+(d+3)*129600*((3 : ℝ)^(d+1))^3)*
      L^(d+1)*ρ^2*θ^2*(1+Real.log L)^2 := by
  have hb := Counting.card_dense_dot_product_strips_le s c hρ hθ hscale hρL hbox hdense
  have hθsq : 1 ≤ θ^2 := by nlinarith only [hθ]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogsq : 1 ≤ (1+Real.log L)^2 := by nlinarith only [hlog,sq_nonneg (Real.log L)]
  have hsmall : ρ^(d+3) ≤ L^(d+1)*ρ^2*θ^2*(1+Real.log L)^2 := by
    calc
      _ = ρ^(d+1)*ρ^2 := by rw [← pow_add]
      _ ≤ L^(d+1)*ρ^2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρL _) (sq_nonneg _)
      _ ≤ L^(d+1)*ρ^2*θ^2 := le_mul_of_one_le_right (by positivity) hθsq
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlogsq
  have hK : 0 ≤ (5 : ℝ)^(d+3)+(d+3)*129600*((3 : ℝ)^(d+1))^3 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsmall hK
  nlinarith only [hb,hm]

end WaveTurbulence.CountLemmas
