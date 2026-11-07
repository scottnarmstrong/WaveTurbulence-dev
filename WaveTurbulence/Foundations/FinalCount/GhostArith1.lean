/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostCount
/-! G2-GHOST part 4: the real inequalities, part 1: the `ν`-slab factor. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- **The `ν`-slab factor**: a slab whose normal has a coordinate of size `Q L / (2 d)`
costs `≲ P^c L^{-γ}/Q` after the factor `L^{-(d-γ)}`. -/
theorem Fnu_bound (d : ℕ) {L γ η δ C₁ na Q ρ : ℝ} (c : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQl : L⁻¹ ≤ Q) (hQu : Q ≤ L ^ (-γ + η)) (hρ : ρ = Q / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        L ^ (-((d : ℝ) - γ)) * qq δ C₁ ≤
      9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * (L ^ (-γ) / Q) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hP1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hPc : 1 ≤ Real.log L ^ c := one_le_pow₀ hP1
  have hq := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hδ1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).2 hδ
  have h5 := two_m_succ_le hL1
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  set X : ℝ := L ^ (2 - 2 * γ) with hX
  have hslab : na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 = na * δ⁻¹ * X := by
    have : L ^ (-2 * γ) * L ^ 2 = X := by
      rw [hX, show (2 - 2 * γ) = -2 * γ + (2 : ℕ) by push_cast; ring, Real.rpow_add hL0, Real.rpow_natCast]
    calc na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 = na * δ⁻¹ * (L ^ (-2 * γ) * L ^ 2) := by ring
      _ = _ := by rw [this]
  rw [hslab]
  set A : ℝ := 2 * (2 * (na * δ⁻¹ * X)) / (ρ * L / d) with hA
  have hA0 : 0 ≤ A := by
    rw [hA, hρ]; positivity
  have hAe : A = 8 * d * na * δ⁻¹ * X / (Q * L) := by
    rw [hA, hρ]; field_simp; ring
  have hfl : (((⌊A⌋₊ + 1 : ℕ)) : ℝ) ≤ A + 1 := by
    push_cast
    have := Nat.floor_le hA0
    linarith
  have hm : (((2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) ≤ 5 ^ (d - 1) * L ^ (d - 1) := by
    push_cast
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h5) _
  have hN : (((⌊A⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) ≤ (A + 1) * (5 ^ (d - 1) * L ^ (d - 1)) := by
    push_cast
    push_cast at hm hfl
    exact mul_le_mul hfl hm (by positivity) (by positivity)
  have hexp : L ^ (d - 1) * L ^ (-((d : ℝ) - γ)) = L ^ (γ - 1) := by
    rw [← Real.rpow_natCast L (d - 1), ← Real.rpow_add hL0]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]; ring
  -- A L^{γ-1} = 8 d na δ⁻¹ L^{-γ} / Q
  have hAL : A * L ^ (γ - 1) = 8 * d * na * δ⁻¹ * (L ^ (-γ) / Q) := by
    rw [hAe]
    have : X * L ^ (γ - 1) = L ^ (-γ + 1) := by
      rw [hX, ← Real.rpow_add hL0]; congr 1; ring
    have h2 : L ^ (-γ + 1) = L ^ (-γ) * L := by
      rw [Real.rpow_add hL0, Real.rpow_one]
    calc 8 * d * na * δ⁻¹ * X / (Q * L) * L ^ (γ - 1) = 8 * d * na * δ⁻¹ * (X * L ^ (γ - 1)) / (Q * L) := by ring
      _ = 8 * d * na * δ⁻¹ * (L ^ (-γ) * L) / (Q * L) := by rw [this, h2]
      _ = _ := by field_simp
  -- L^{γ-1} ≤ L^{-γ} / Q
  have hsm : L ^ (γ - 1) ≤ L ^ (-γ) / Q := by
    rw [le_div_iff₀ hQ0]
    calc L ^ (γ - 1) * Q ≤ L ^ (γ - 1) * L ^ (-γ + η) :=
          mul_le_mul_of_nonneg_left hQu (Real.rpow_nonneg hL0.le _)
      _ = L ^ (η - 1) := by rw [← Real.rpow_add hL0]; congr 1; ring
      _ ≤ L ^ (-γ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hK : 0 ≤ L ^ (-γ) / Q := by positivity
  calc (((⌊A⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) * L ^ (-((d : ℝ) - γ)) * qq δ C₁
      ≤ (A + 1) * (5 ^ (d - 1) * L ^ (d - 1)) * L ^ (-((d : ℝ) - γ)) * qq δ C₁ := by gcongr
    _ = 5 ^ (d - 1) * (A * L ^ (γ - 1) + L ^ (γ - 1)) * qq δ C₁ := by
        rw [← hexp]; ring
    _ ≤ 5 ^ (d - 1) * (8 * d * na * δ⁻¹ * (L ^ (-γ) / Q) + L ^ (-γ) / Q) * qq δ C₁ := by
        rw [hAL]; gcongr
    _ ≤ 5 ^ d * (9 * d * δ⁻¹ * Real.log L ^ c * (L ^ (-γ) / Q)) * qq δ C₁ := by
        have h51 : (5 : ℝ) ^ (d - 1) ≤ 5 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
        have hin : 8 * d * na * δ⁻¹ * (L ^ (-γ) / Q) + L ^ (-γ) / Q ≤ 9 * d * δ⁻¹ * Real.log L ^ c * (L ^ (-γ) / Q) := by
          have h1 : 8 * d * na * δ⁻¹ ≤ 8 * d * Real.log L ^ c * δ⁻¹ := by gcongr
          have h2 : (1 : ℝ) ≤ d * δ⁻¹ * Real.log L ^ c := by
            calc (1 : ℝ) = 1 * 1 * 1 := by ring
              _ ≤ _ := by gcongr; linarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hK, mul_le_mul_of_nonneg_right h2 hK]
        have hp : 0 ≤ 9 * d * δ⁻¹ * Real.log L ^ c * (L ^ (-γ) / Q) := by positivity
        calc 5 ^ (d - 1) * (8 * d * na * δ⁻¹ * (L ^ (-γ) / Q) + L ^ (-γ) / Q) * qq δ C₁
            ≤ 5 ^ (d - 1) * (9 * d * δ⁻¹ * Real.log L ^ c * (L ^ (-γ) / Q)) * qq δ C₁ := by gcongr
          _ ≤ 5 ^ d * (9 * d * δ⁻¹ * Real.log L ^ c * (L ^ (-γ) / Q)) * qq δ C₁ := by gcongr
    _ = _ := by ring

end WaveTurbulence.FinalCount
