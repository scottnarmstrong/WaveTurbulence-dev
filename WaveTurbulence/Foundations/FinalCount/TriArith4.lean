/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriArith3
/-! Triangles, part 19 (FINALCOUNT-G2): the arithmetic for `ΔF = 1` and `ΔF = 0`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- **`ΔF = 1`.** -/
theorem arith_ba (d : ℕ) {L γ η δ C₁ na R ρ : ℝ} (c κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R)) :
    (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
        Real.log L ^ 12 ≤
      (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * excessRHS L γ η [(R, κ)] 1 2 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hF := F1_bound d c hd hγ0 hγ1 hL hδ0 hδ hC hna0 hna
  have hA := atom_factor d κ hd hγ0 hγ1 hη hη1 hη2 hL hRl hRu hρ
  have hq0 := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hdq2 := delta_inv_qq_sq hδ0 hC
  rw [rankFactor_nat d L γ δ C₁ hL0 2, excessRHS_ba L γ η R κ hL0]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  set F : ℝ := ((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) with hFdef
  set B : ℝ := (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d with hBdef
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by positivity
  have hN : (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) = F * B := by
    rw [hFdef, hBdef]; push_cast; ring
  rw [hN]
  set P := Real.log L with hP
  have hP0 : 0 ≤ P := Real.log_nonneg hL1
  have hexp : L ^ (min γ (1 - γ)) * (L ^ (η ^ 2) * L ^ (-(3 * γ / 2 - η / 2))) ≤ L ^ (-η ^ 3 + η ^ 2) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have h1 : min γ (1 - γ) ≤ γ := min_le_left _ _
    have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
    nlinarith
  calc F * B * ((L ^ (-((d : ℝ) - γ))) ^ 2 * qq δ C₁ ^ 2) * P ^ 12
      = (F * L ^ (-((d : ℝ) - γ)) * qq δ C₁) * (B * L ^ (-((d : ℝ) - γ))) * qq δ C₁ * P ^ 12 := by ring
    _ ≤ (3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * P ^ c * L ^ (min γ (1 - γ))) *
          (5 ^ d * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) * L ^ (-(3 * γ / 2 - η / 2))) * qq δ C₁ * P ^ 12 := by
        gcongr
    _ = (3 * 5 ^ d * 5 ^ d) * (δ⁻¹ * qq δ C₁ ^ 2) * P ^ (c + 12) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by ring
    _ ≤ (3 * 5 ^ d * 5 ^ d) * 1 * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        have h1 : (3 * 5 ^ d * 5 ^ d : ℝ) * (δ⁻¹ * qq δ C₁ ^ 2) ≤ (3 * 5 ^ d * 5 ^ d) * 1 :=
          mul_le_mul_of_nonneg_left hdq2 (by positivity)
        have hLm : 0 ≤ L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)) := by positivity
        have h2 := mul_le_mul h1 hlog (by positivity) (by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 hLm
        have h4 := mul_le_mul_of_nonneg_right h3 hT
        nlinarith [h4]
    _ = (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
          (L ^ (min γ (1 - γ)) * (L ^ (η ^ 2) * L ^ (-(3 * γ / 2 - η / 2)))) *
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by ring
    _ ≤ (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * L ^ (-η ^ 3 + η ^ 2) *
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        gcongr
    _ = _ := by ring

/-- **`ΔF = 0`.** -/
theorem arith_aa (d : ℕ) {L γ η δ C₁ R₀ R₁ ρ₀ ρ₁ : ℝ} (κ₀ κ₁ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hC : 1 ≤ C₁)
    (hδ : δ ≤ 1)
    (hRl₀ : L⁻¹ ≤ R₀) (hRu₀ : R₀ ≤ L ^ (-γ + η)) (hρ₀ : (κ₀ = 0 ∧ ρ₀ = 2 * R₀) ∨ (κ₀ = 50 ∧ ρ₀ = L ^ (-50 * η) * R₀))
    (hRl₁ : L⁻¹ ≤ R₁) (hRu₁ : R₁ ≤ L ^ (-γ + η)) (hρ₁ : (κ₁ = 0 ∧ ρ₁ = 2 * R₁) ∨ (κ₁ = 50 ∧ ρ₁ = L ^ (-50 * η) * R₁)) :
    (((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((3 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12) *
        excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hA0 := atom_factor d κ₀ hd hγ0 hγ1 hη hη1 hη2 hL hRl₀ hRu₀ hρ₀
  have hA1 := atom_factor d κ₁ hd hγ0 hγ1 hη hη1 hη2 hL hRl₁ hRu₁ hρ₁
  have hq0 := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hq1 := qq_le_one hδ0 hδ hC
  rw [rankFactor_nat d L γ δ C₁ hL0 3, excessRHS_aa L γ η R₀ R₁ κ₀ κ₁ hL0]
  have hlog := log_pow_le_eta 12 (by omega) hL1 hη
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  have hLd := rpow_nat_mul_neg d (γ := γ) hL0
  have h5 := two_m_succ_le hL1
  set P := Real.log L with hP
  have hP0 : 0 ≤ P := Real.log_nonneg hL1
  set T₀ := L ^ ((γ + 3 * η) / 2 - (κ₀ : ℝ) * η) * R₀ with hT₀
  set T₁ := L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * R₁ with hT₁
  have hRp₀ : 0 < R₀ := lt_of_lt_of_le (inv_pos.2 hL0) hRl₀
  have hRp₁ : 0 < R₁ := lt_of_lt_of_le (inv_pos.2 hL0) hRl₁
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hT₁0 : 0 ≤ T₁ := by positivity
  set B₀ : ℝ := (((⌊2 * ρ₀ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d with hB₀
  set B₁ : ℝ := (((⌊2 * ρ₁ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d with hB₁
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hM : (((2 * ⌊2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) * L ^ (-((d : ℝ) - γ)) ≤ 5 ^ d * L ^ γ := by
    push_cast
    calc ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d) * L ^ (-((d : ℝ) - γ)) ≤ (5 * L) ^ d * L ^ (-((d : ℝ) - γ)) := by
          gcongr
          exact_mod_cast h5
      _ = 5 ^ d * (L ^ d * L ^ (-((d : ℝ) - γ))) := by rw [mul_pow]; ring
      _ = 5 ^ d * L ^ γ := by rw [hLd]
  have hexp : L ^ γ * (L ^ (η ^ 2) * (L ^ (-(3 * γ / 2 - η / 2)) * L ^ (-(3 * γ / 2 - η / 2)))) ≤
      L ^ (-η ^ 3 - (min γ (1 - γ) + 2 * η ^ 2)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have h1 : min γ (1 - γ) ≤ γ := min_le_left _ _
    have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
    have h2 : η ^ 2 ≤ η := by nlinarith
    nlinarith
  push_cast
  calc ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d * ((((⌊2 * ρ₀ * L⌋₊ : ℝ) + 1)) ^ d * (((⌊2 * ρ₁ * L⌋₊ : ℝ) + 1)) ^ d)) *
        ((L ^ (-((d : ℝ) - γ))) ^ 3 * qq δ C₁ ^ 3) * P ^ 12
      = (((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d) * L ^ (-((d : ℝ) - γ))) * (B₀ * L ^ (-((d : ℝ) - γ))) *
          (B₁ * L ^ (-((d : ℝ) - γ))) * qq δ C₁ ^ 3 * P ^ 12 := by
        simp only [hB₀, hB₁]; push_cast; ring
    _ ≤ (5 ^ d * L ^ γ) * (5 ^ d * T₀ * L ^ (-(3 * γ / 2 - η / 2))) * (5 ^ d * T₁ * L ^ (-(3 * γ / 2 - η / 2))) * 1 * P ^ 12 := by
        have hq3 : qq δ C₁ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
        have hM' : (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d * L ^ (-((d : ℝ) - γ)) ≤ 5 ^ d * L ^ γ := by
          have := hM; push_cast at this; exact this
        gcongr
    _ = (5 ^ d * 5 ^ d * 5 ^ d) * P ^ 12 * (L ^ γ * (L ^ (-(3 * γ / 2 - η / 2)) * L ^ (-(3 * γ / 2 - η / 2)))) * (T₀ * T₁) := by ring
    _ ≤ (5 ^ d * 5 ^ d * 5 ^ d) * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12 * L ^ (η ^ 2) *
          (L ^ γ * (L ^ (-(3 * γ / 2 - η / 2)) * L ^ (-(3 * γ / 2 - η / 2)))) * (T₀ * T₁) := by
        have hnn : 0 ≤ (5 ^ d * 5 ^ d * 5 ^ d : ℝ) * (L ^ γ * (L ^ (-(3 * γ / 2 - η / 2)) * L ^ (-(3 * γ / 2 - η / 2)))) * (T₀ * T₁) := by positivity
        have key := mul_le_mul_of_nonneg_left hlog hnn
        linarith [key]
    _ = (5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12) *
          (L ^ γ * (L ^ (η ^ 2) * (L ^ (-(3 * γ / 2 - η / 2)) * L ^ (-(3 * γ / 2 - η / 2))))) * (T₀ * T₁) := by ring
    _ ≤ (5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12) * L ^ (-η ^ 3 - (min γ (1 - γ) + 2 * η ^ 2)) * (T₀ * T₁) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.FinalCount
