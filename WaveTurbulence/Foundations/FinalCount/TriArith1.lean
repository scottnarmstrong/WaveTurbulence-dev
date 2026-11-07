/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Cut
public import WaveTurbulence.Foundations.FinalCount.TriCount6
/-! Triangles, part 16 (FINALCOUNT-G2): the real inequalities. Per-`α`-atom factor
`(⌊2ρL⌋+1)^d L^{-(d-γ)} ≤ 5^d L^{(γ+3η)/2-κη} R · L^{-(3γ/2-η/2)}`, `ρ = 2R` (`κ = 0`) or `ρ = L^{-50η}R` (`κ = 50`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem R_pow_le (d : ℕ) {L γ η R : ℝ} (hd : 3 ≤ d) (hL1 : 1 ≤ L) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hRu : R ≤ L ^ (-γ + η)) (hη : η ≤ γ) :
    R ^ d ≤ R * L ^ (-2 * γ + 2 * η) := by
  have hL0 : 0 < L := by linarith
  have h2 : R ^ 2 ≤ L ^ (-2 * γ + 2 * η) := by
    calc R ^ 2 ≤ (L ^ (-γ + η)) ^ 2 := pow_le_pow_left₀ hR0 hRu 2
      _ = L ^ (-2 * γ + 2 * η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have h3 : R ^ (d - 1) ≤ R ^ 2 := pow_le_pow_of_le_one hR0 hR1 (by omega)
  calc R ^ d = R * R ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_left h3 hR0
    _ ≤ R * L ^ (-2 * γ + 2 * η) := mul_le_mul_of_nonneg_left h2 hR0

/-- **The per-atom factor.** -/
theorem atom_factor (d : ℕ) {L γ η R ρ : ℝ} (κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hRl : L⁻¹ ≤ R)
    (hRu : R ≤ L ^ (-γ + η)) (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R)) :
    (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d * L ^ (-((d : ℝ) - γ)) ≤
      5 ^ d * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) * L ^ (-(3 * γ / 2 - η / 2)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hR0 : 0 ≤ R := hRpos.le
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  have hRL : 1 ≤ R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hRd := R_pow_le d (γ := γ) (η := η) hd hL1 hR0 hR1 hRu (by linarith)
  have hLd := rpow_nat_mul_neg d (γ := γ) hL0
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · positivity
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0
  have hfl : (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * ρ * L + 1 := by
    push_cast
    have := Nat.floor_le (a := 2 * ρ * L) (by positivity)
    linarith
  have hfl0 : (0 : ℝ) ≤ (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) := by positivity
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  rcases hρ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- κ = 0
    have h1 : (((⌊2 * (2 * R) * L⌋₊ + 1 : ℕ) : ℝ)) ≤ 5 * (R * L) := by nlinarith
    have h2 : (((⌊2 * (2 * R) * L⌋₊ + 1 : ℕ) : ℝ)) ^ d ≤ (5 * (R * L)) ^ d := pow_le_pow_left₀ hfl0 h1 d
    calc (((⌊2 * (2 * R) * L⌋₊ + 1 : ℕ) : ℝ)) ^ d * L ^ (-((d : ℝ) - γ)) ≤ (5 * (R * L)) ^ d * L ^ (-((d : ℝ) - γ)) :=
          mul_le_mul_of_nonneg_right h2 hLn
      _ = 5 ^ d * R ^ d * (L ^ d * L ^ (-((d : ℝ) - γ))) := by rw [mul_pow, mul_pow]; ring
      _ = 5 ^ d * R ^ d * L ^ γ := by rw [hLd]
      _ ≤ 5 ^ d * (R * L ^ (-2 * γ + 2 * η)) * L ^ γ := by
          gcongr
      _ = 5 ^ d * (L ^ ((γ + 3 * η) / 2 - (((0 : ℕ) : ℝ)) * η) * R) * L ^ (-(3 * γ / 2 - η / 2)) := by
          have : L ^ (-2 * γ + 2 * η) * L ^ γ = L ^ ((γ + 3 * η) / 2 - (((0 : ℕ) : ℝ)) * η) * L ^ (-(3 * γ / 2 - η / 2)) := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; push_cast; ring
          calc 5 ^ d * (R * L ^ (-2 * γ + 2 * η)) * L ^ γ = 5 ^ d * R * (L ^ (-2 * γ + 2 * η) * L ^ γ) := by ring
            _ = _ := by rw [this]; ring
  · -- κ = 50
    set ρ := L ^ (-50 * η) * R with hρdef
    have hL50 : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have hL50n : 0 ≤ L ^ (-50 * η) := Real.rpow_nonneg hL0.le _
    have hrhs : 5 ^ d * (L ^ ((γ + 3 * η) / 2 - (((50 : ℕ) : ℝ)) * η) * R) * L ^ (-(3 * γ / 2 - η / 2)) =
        5 ^ d * R * L ^ (-γ - 48 * η) := by
      have : L ^ ((γ + 3 * η) / 2 - (((50 : ℕ) : ℝ)) * η) * L ^ (-(3 * γ / 2 - η / 2)) = L ^ (-γ - 48 * η) := by
        rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
      calc _ = 5 ^ d * R * (L ^ ((γ + 3 * η) / 2 - (((50 : ℕ) : ℝ)) * η) * L ^ (-(3 * γ / 2 - η / 2))) := by ring
        _ = _ := by rw [this]
    rw [hrhs]
    by_cases hA : 1 ≤ 2 * ρ * L
    · have h1 : (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ≤ 4 * (ρ * L) := by nlinarith
      have h2 : (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d ≤ (4 * (ρ * L)) ^ d := pow_le_pow_left₀ hfl0 h1 d
      have hρd : ρ ^ d ≤ L ^ (-150 * η) * R ^ d := by
        rw [hρdef, mul_pow]
        have h3 : (L ^ (-50 * η)) ^ d ≤ (L ^ (-50 * η)) ^ 3 := pow_le_pow_of_le_one hL50n hL50 hd
        have h4 : (L ^ (-50 * η)) ^ 3 = L ^ (-150 * η) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
        rw [h4] at h3
        exact mul_le_mul_of_nonneg_right h3 (pow_nonneg hR0 _)
      calc (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d * L ^ (-((d : ℝ) - γ)) ≤ (4 * (ρ * L)) ^ d * L ^ (-((d : ℝ) - γ)) :=
            mul_le_mul_of_nonneg_right h2 hLn
        _ = 4 ^ d * ρ ^ d * (L ^ d * L ^ (-((d : ℝ) - γ))) := by rw [mul_pow, mul_pow]; ring
        _ = 4 ^ d * ρ ^ d * L ^ γ := by rw [hLd]
        _ ≤ 4 ^ d * (L ^ (-150 * η) * R ^ d) * L ^ γ := by gcongr
        _ ≤ 4 ^ d * (L ^ (-150 * η) * (R * L ^ (-2 * γ + 2 * η))) * L ^ γ := by gcongr
        _ = 4 ^ d * R * L ^ (-γ - 148 * η) := by
            have : L ^ (-150 * η) * L ^ (-2 * γ + 2 * η) * L ^ γ = L ^ (-γ - 148 * η) := by
              rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
            calc _ = 4 ^ d * R * (L ^ (-150 * η) * L ^ (-2 * γ + 2 * η) * L ^ γ) := by ring
              _ = _ := by rw [this]
        _ ≤ 5 ^ d * R * L ^ (-γ - 48 * η) := by
            have h5 : (4 : ℝ) ^ d ≤ 5 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
            have h6 : L ^ (-γ - 148 * η) ≤ L ^ (-γ - 48 * η) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
            gcongr
    · push Not at hA
      have h1 : (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 := by linarith
      have h2 : (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d ≤ 2 ^ d := pow_le_pow_left₀ hfl0 h1 d
      have h3 : L ^ (-((d : ℝ) - γ)) ≤ L ^ (-1 - γ - 48 * η) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have h4 : L ^ (-1 - γ - 48 * η) = L⁻¹ * L ^ (-γ - 48 * η) := by
        rw [show (-1 - γ - 48 * η) = -1 + (-γ - 48 * η) by ring, Real.rpow_add hL0, Real.rpow_neg_one]
      calc (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d * L ^ (-((d : ℝ) - γ)) ≤ 2 ^ d * L ^ (-1 - γ - 48 * η) :=
            mul_le_mul h2 h3 hLn (by positivity)
        _ = 2 ^ d * (L⁻¹ * L ^ (-γ - 48 * η)) := by rw [h4]
        _ ≤ 5 ^ d * R * L ^ (-γ - 48 * η) := by
            have h5 : (2 : ℝ) ^ d ≤ 5 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
            have hp : 0 ≤ L ^ (-γ - 48 * η) := Real.rpow_nonneg hL0.le _
            calc 2 ^ d * (L⁻¹ * L ^ (-γ - 48 * η)) ≤ 5 ^ d * (R * L ^ (-γ - 48 * η)) := by
                  gcongr
              _ = _ := by ring

end WaveTurbulence.FinalCount
