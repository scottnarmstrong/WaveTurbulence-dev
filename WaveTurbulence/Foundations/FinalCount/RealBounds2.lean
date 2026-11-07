/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RealBounds1
/-! Real bounds for the `α`-cut (FINALCOUNT-G2 step 4): the shared estimate and `κ = 0`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem E_bound (d : ℕ) {L γ η R : ℝ} (hd : 3 ≤ d) (hL : 1 ≤ L) (hη : 0 < η) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hRu : R ≤ L ^ (-γ + η)) :
    R ^ d * (8 * R * L ^ (2 * γ) + 5) ≤ 13 * R ^ 2 * L ^ (2 * η) := by
  have hL0 : 0 < L := by linarith
  have h1 : R ^ d ≤ R ^ 3 := pow_le_pow_of_le_one hR0 hR1 hd
  have h2 : R * L ^ γ ≤ L ^ η := by
    calc R * L ^ γ ≤ L ^ (-γ + η) * L ^ γ :=
          mul_le_mul_of_nonneg_right hRu (Real.rpow_nonneg hL0.le _)
      _ = L ^ η := by rw [← Real.rpow_add hL0]; congr 1; ring
  have h3 : L ^ (2 * γ) = (L ^ γ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have h4 : L ^ (2 * η) = (L ^ η) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have h5 : 1 ≤ L ^ (2 * η) := Real.one_le_rpow hL (by linarith)
  have h6 : (R * L ^ γ) ^ 2 ≤ (L ^ η) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have hpos : 0 ≤ 8 * R * L ^ (2 * γ) + 5 := by positivity
  calc R ^ d * (8 * R * L ^ (2 * γ) + 5) ≤ R ^ 3 * (8 * R * L ^ (2 * γ) + 5) :=
        mul_le_mul_of_nonneg_right h1 hpos
    _ = 8 * R ^ 2 * (R * L ^ γ) ^ 2 + 5 * R ^ 3 := by rw [h3]; ring
    _ ≤ 8 * R ^ 2 * (L ^ η) ^ 2 + 5 * R ^ 2 * L ^ (2 * η) := by
        have : R ^ 3 ≤ R ^ 2 := pow_le_pow_of_le_one hR0 hR1 (by norm_num)
        have h7 : 5 * R ^ 3 ≤ 5 * R ^ 2 * L ^ (2 * η) := by
          nlinarith [sq_nonneg R, pow_nonneg hR0 2]
        have h8 : 8 * R ^ 2 * (R * L ^ γ) ^ 2 ≤ 8 * R ^ 2 * (L ^ η) ^ 2 :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        linarith
    _ = 13 * R ^ 2 * L ^ (2 * η) := by rw [h4]; ring

/-- `α`-cut with `κ = 0` and `ρ = 2R`. -/
theorem alphaDev_kappa0 (d : ℕ) {L γ η δ C₁ R : ℝ} (hd : 3 ≤ d) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hγη : η ≤ γ) :
    (alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R (2 * R) : ℝ) *
        (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4) ≤
      (26 * 5 ^ d * (8 / η) ^ 4) * (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2) * R) ^ 2) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR0 : 0 ≤ R := (inv_nonneg.2 hL0.le).trans hRl
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  have hRL : 1 ≤ R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hred := alphaDev_reduce d (γ := γ) (C₁ := C₁) hL1 hδ0 hδ hC hR0 (by linarith : 0 ≤ 2 * R)
  refine hred.trans ?_
  have hA : (2 * (2 * R) * L + 1) ^ d ≤ 5 ^ d * (R ^ d * L ^ d) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hE := E_bound d (γ := γ) hd hL1 hη hR0 hR1 hRu
  have hlog := log_pow_four_le L (η / 2) hL1 (by linarith)
  have hLd := rpow_nat_mul_neg d (γ := γ) hL0
  have hLg : 0 ≤ L ^ γ := Real.rpow_nonneg hL0.le _
  have hlog0 : 0 ≤ Real.log L ^ 4 := by have := Real.log_nonneg hL1; positivity
  have hexp : L ^ (γ + 2 * η + η / 2) ≤ L ^ (-η ^ 3) * L ^ (γ + 3 * η) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith [sq_nonneg η, pow_pos hη 3])
  have hrhs : (L ^ ((γ + 3 * η) / 2) * R) ^ 2 = L ^ (γ + 3 * η) * R ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 2; push_cast; ring
  rw [hrhs]
  -- assemble
  have hmain : (2 * (2 * R) * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) *
      (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) ≤
      26 * 5 ^ d * (R ^ 2 * L ^ (2 * η)) * L ^ γ * Real.log L ^ 4 := by
    calc _ ≤ (5 ^ d * (R ^ d * L ^ d)) * (2 * (8 * R * L ^ (2 * γ) + 5)) *
          (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) := by
          gcongr
      _ = 2 * 5 ^ d * (R ^ d * (8 * R * L ^ (2 * γ) + 5)) * (L ^ d * L ^ (-((d : ℝ) - γ))) *
            Real.log L ^ 4 := by ring
      _ = 2 * 5 ^ d * (R ^ d * (8 * R * L ^ (2 * γ) + 5)) * L ^ γ * Real.log L ^ 4 := by rw [hLd]
      _ ≤ 2 * 5 ^ d * (13 * R ^ 2 * L ^ (2 * η)) * L ^ γ * Real.log L ^ 4 := by gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  have h5 : (0 : ℝ) ≤ 26 * 5 ^ d * (R ^ 2 * L ^ (2 * η)) * L ^ γ := by positivity
  calc 26 * 5 ^ d * (R ^ 2 * L ^ (2 * η)) * L ^ γ * Real.log L ^ 4
      ≤ 26 * 5 ^ d * (R ^ 2 * L ^ (2 * η)) * L ^ γ * ((4 / (η / 2)) ^ 4 * L ^ (η / 2)) :=
        mul_le_mul_of_nonneg_left hlog h5
    _ = 26 * 5 ^ d * (4 / (η / 2)) ^ 4 * R ^ 2 * (L ^ (2 * η) * L ^ γ * L ^ (η / 2)) := by ring
    _ = 26 * 5 ^ d * (4 / (η / 2)) ^ 4 * R ^ 2 * L ^ (γ + 2 * η + η / 2) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 2; ring
    _ ≤ 26 * 5 ^ d * (4 / (η / 2)) ^ 4 * R ^ 2 * (L ^ (-η ^ 3) * L ^ (γ + 3 * η)) := by
        gcongr
    _ = _ := by rw [show (4 / (η / 2)) = 8 / η by field_simp; ring]; ring

end WaveTurbulence.FinalCount
