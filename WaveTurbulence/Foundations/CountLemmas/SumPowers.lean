/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.StripPowers

/-! # The exact power saving in the sum-variable triple count -/

public section
namespace WaveTurbulence.CountLemmas

/-- Both terms from the atomic shell count satisfy the requested triple
power, including γ=1/2 without a logarithmic loss. -/
theorem sum_triple_power_bound (n : ℕ) {C L δ γ : ℝ} (hC : 0 ≤ C)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let τ := δ⁻¹*L^(-2*γ)
    C*τ*L^(2*((n+2 : ℕ) : ℝ))*(2*L+1)^n*(2*τ*L^2+L) ≤
      (3*C*3^n)*δ⁻¹^2*L^(3*((n+2 : ℕ) : ℝ)-3*γ-min γ (1-γ)) := by
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let D : ℝ := (n+2 : ℕ)
  let E : ℝ := 3*D-3*γ-min γ (1-γ)
  have hτ : 0 < δ⁻¹*L^(-2*γ) := mul_pos (inv_pos.mpr hδ) (Real.rpow_pos_of_pos hLp _)
  have hbox : (2*L+1)^n ≤ 3^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) n
  have h₁ : L^(3*D-4*γ) ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL (by
    dsimp only [E]
    linarith only [min_le_left γ (1-γ)])
  have h₂ : L^(3*D-1-2*γ) ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL (by
    dsimp only [E]
    linarith only [min_le_right γ (1-γ)])
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hδsq : δ⁻¹ ≤ δ⁻¹^2 := by nlinarith only [hδi]
  have hmon₁ : δ⁻¹^2*L^(3*D-4*γ) ≤ δ⁻¹^2*L^E := mul_le_mul_of_nonneg_left h₁ (sq_nonneg _)
  have hmon₂ : δ⁻¹*L^(3*D-1-2*γ) ≤ δ⁻¹^2*L^E :=
    mul_le_mul hδsq h₂ (Real.rpow_nonneg hLp.le _) (sq_nonneg _)
  have hid₁ : (δ⁻¹*L^(-2*γ))^2*L^(2*D)*L^n*L^2 = δ⁻¹^2*L^(3*D-4*γ) := by
    rw [mul_pow,← Real.rpow_mul_natCast hLp.le,← Real.rpow_natCast L n,← Real.rpow_natCast L 2]
    calc
      _ = δ⁻¹^2*(L^((-2*γ)*(2 : ℝ))*L^(2*D)*L^(n : ℝ)*L^(2 : ℝ)) := by norm_num only [Nat.cast_ofNat]; ring
      _ = _ := by
        rw [← Real.rpow_add hLp,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 2
        dsimp only [D]
        push_cast
        ring
  have hid₂ : (δ⁻¹*L^(-2*γ))*L^(2*D)*L^n*L = δ⁻¹*L^(3*D-1-2*γ) := by
    rw [← Real.rpow_natCast L n]
    calc
      _ = δ⁻¹*(L^(-2*γ)*L^(2*D)*L^(n : ℝ)*L^(1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_add hLp,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 2
        dsimp only [D]
        push_cast
        ring
  calc
    _ ≤ C*(δ⁻¹*L^(-2*γ))*L^(2*D)*(3^n*L^n)*(2*(δ⁻¹*L^(-2*γ))*L^2+L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbox (by positivity)) (by positivity)
    _ = C*3^n*(2*(δ⁻¹^2*L^(3*D-4*γ))+δ⁻¹*L^(3*D-1-2*γ)) := by
      calc
        _ = C*3^n*(2*((δ⁻¹*L^(-2*γ))^2*L^(2*D)*L^n*L^2)+
          (δ⁻¹*L^(-2*γ))*L^(2*D)*L^n*L) := by ring
        _ = _ := by rw [hid₁,hid₂]
    _ ≤ C*3^n*(3*(δ⁻¹^2*L^E)) := mul_le_mul_of_nonneg_left
      (by linarith only [hmon₁,hmon₂]) (by positivity)
    _ = _ := by dsimp only [E,D]; ring

end WaveTurbulence.CountLemmas
