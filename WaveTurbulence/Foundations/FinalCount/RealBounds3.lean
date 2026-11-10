/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RealBounds2
/-! Real bounds for the `α`-cut (FINALCOUNT-G2 step 4): `κ = 50`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem const_le_a (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (3 : ℝ) ^ d * a ≤ 5 ^ d * (a + b) := by
  have h1 : (3 : ℝ) ^ d ≤ 5 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h2 : 0 ≤ (5 : ℝ) ^ d := by positivity
  calc (3 : ℝ) ^ d * a ≤ 5 ^ d * a := mul_le_mul_of_nonneg_right h1 ha
    _ ≤ 5 ^ d * (a + b) := mul_le_mul_of_nonneg_left (by linarith) h2

theorem const_le_b (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (3 : ℝ) ^ d * b ≤ 5 ^ d * (a + b) := by
  have := const_le_a d hb ha
  linarith

/-- `α`-cut with `κ = 50` and the ball radius `ρ = L^{-50η} R`. -/
theorem alphaDev_kappa50 (d : ℕ) {L γ η δ C₁ R : ℝ} (hd : 3 ≤ d) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hηγ : η ≤ (1 - γ) / 200) (hγ1 : γ < 1)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hγη : η ≤ γ) :
    (alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R (L ^ (-50 * η) * R) : ℝ) *
        (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4) ≤
      (26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - 50 * η) * R) ^ 2) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR0 : 0 ≤ R := (inv_nonneg.2 hL0.le).trans hRl
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hρ0 : 0 ≤ L ^ (-50 * η) * R := mul_nonneg (Real.rpow_nonneg hL0.le _) hR0
  have hred := alphaDev_reduce d (γ := γ) (C₁ := C₁) hL1 hδ0 hδ hC hR0 hρ0
  refine hred.trans ?_
  have hE := E_bound d (γ := γ) hd hL1 hη hR0 hR1 hRu
  have hlogη := log_pow_four_le L (η / 2) hL1 (by linarith)
  have hlog1 := log_pow_four_le L ((1 - γ) / 2) hL1 (by linarith)
  have hLd := rpow_nat_mul_neg d (γ := γ) hL0
  have hLg : 0 ≤ L ^ γ := Real.rpow_nonneg hL0.le _
  have hlog0 : 0 ≤ Real.log L ^ 4 := by have := Real.log_nonneg hL1; positivity
  have hrhs : (L ^ ((γ + 3 * η) / 2 - 50 * η) * R) ^ 2 = L ^ (γ + 3 * η - 100 * η) * R ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 2; push_cast; ring
  rw [hrhs]
  have hη3 : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
  set ρ := L ^ (-50 * η) * R with hρdef
  have hL50 : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  by_cases hρL : 1 ≤ ρ * L
  · -- case A
    have h3 : (2 * ρ * L + 1) ^ d ≤ 3 ^ d * (ρ ^ d * L ^ d) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) d
    have hρd : ρ ^ d ≤ L ^ (-150 * η) * R ^ d := by
      rw [hρdef, mul_pow]
      have h1 : (L ^ (-50 * η)) ^ d ≤ (L ^ (-50 * η)) ^ 3 :=
        pow_le_pow_of_le_one (Real.rpow_nonneg hL0.le _) hL50 hd
      have h2 : (L ^ (-50 * η)) ^ 3 = L ^ (-150 * η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
      rw [h2] at h1
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hmain : (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) *
        (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) ≤
        26 * 3 ^ d * (L ^ (-150 * η) * (R ^ 2 * L ^ (2 * η))) * L ^ γ * Real.log L ^ 4 := by
      have hBnn : 0 ≤ 2 * (8 * R * L ^ (2 * γ) + 5) := by positivity
      have hCnn : 0 ≤ L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4 := mul_nonneg (Real.rpow_nonneg hL0.le _) hlog0
      have hA1 : (2 * ρ * L + 1) ^ d ≤ 3 ^ d * ((L ^ (-150 * η) * R ^ d) * L ^ d) :=
        h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρd (by positivity)) (by positivity))
      have hAB : (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) ≤
          (3 ^ d * ((L ^ (-150 * η) * R ^ d) * L ^ d)) * (2 * (8 * R * L ^ (2 * γ) + 5)) :=
        mul_le_mul_of_nonneg_right hA1 hBnn
      have hshape : (3 ^ d * ((L ^ (-150 * η) * R ^ d) * L ^ d)) * (2 * (8 * R * L ^ (2 * γ) + 5)) *
            (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) =
          2 * 3 ^ d * L ^ (-150 * η) * (R ^ d * (8 * R * L ^ (2 * γ) + 5)) * L ^ γ * Real.log L ^ 4 := by
        rw [← hLd]; ring
      have hEE : 2 * 3 ^ d * L ^ (-150 * η) * (R ^ d * (8 * R * L ^ (2 * γ) + 5)) * L ^ γ * Real.log L ^ 4 ≤
          2 * 3 ^ d * L ^ (-150 * η) * (13 * R ^ 2 * L ^ (2 * η)) * L ^ γ * Real.log L ^ 4 := by
        have h0 : 0 ≤ 2 * 3 ^ d * L ^ (-150 * η) := by positivity
        have h1 : 0 ≤ L ^ γ * Real.log L ^ 4 := by positivity
        have := mul_le_mul_of_nonneg_left hE h0
        have := mul_le_mul_of_nonneg_right this h1
        calc _ = 2 * 3 ^ d * L ^ (-150 * η) * (R ^ d * (8 * R * L ^ (2 * γ) + 5)) * (L ^ γ * Real.log L ^ 4) := by ring
          _ ≤ 2 * 3 ^ d * L ^ (-150 * η) * (13 * R ^ 2 * L ^ (2 * η)) * (L ^ γ * Real.log L ^ 4) := this
          _ = _ := by ring
      calc _ ≤ (3 ^ d * ((L ^ (-150 * η) * R ^ d) * L ^ d)) * (2 * (8 * R * L ^ (2 * γ) + 5)) *
            (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) := mul_le_mul_of_nonneg_right hAB hCnn
        _ = _ := hshape
        _ ≤ _ := hEE
        _ = _ := by ring
    refine hmain.trans ?_
    have h5 : (0 : ℝ) ≤ 26 * 3 ^ d * (L ^ (-150 * η) * (R ^ 2 * L ^ (2 * η))) * L ^ γ := by positivity
    have hexp : L ^ (-150 * η) * L ^ (2 * η) * L ^ γ * L ^ (η / 2) ≤ L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hC3 : (3 : ℝ) ^ d * (4 / (η / 2)) ^ 4 ≤ 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4) := by
      have e : 4 / (η / 2) = 8 / η := by field_simp; ring
      rw [e]
      have h8 : 0 ≤ (8 / η) ^ 4 := by positivity
      have hg : 0 < 1 - γ := by linarith
      have h9 : 0 ≤ (8 / (1 - γ)) ^ 4 := by positivity
      exact const_le_a d h8 h9
    calc 26 * 3 ^ d * (L ^ (-150 * η) * (R ^ 2 * L ^ (2 * η))) * L ^ γ * Real.log L ^ 4
        ≤ 26 * 3 ^ d * (L ^ (-150 * η) * (R ^ 2 * L ^ (2 * η))) * L ^ γ * ((4 / (η / 2)) ^ 4 * L ^ (η / 2)) :=
          mul_le_mul_of_nonneg_left hlogη h5
      _ = 26 * (3 ^ d * (4 / (η / 2)) ^ 4) * R ^ 2 * (L ^ (-150 * η) * L ^ (2 * η) * L ^ γ * L ^ (η / 2)) := by ring
      _ ≤ 26 * (5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) * R ^ 2 * (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η)) := by
          have hY : 0 ≤ R ^ 2 * (L ^ (-150 * η) * L ^ (2 * η) * L ^ γ * L ^ (η / 2)) := by positivity
          have hZ : 0 ≤ 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4) := by positivity
          have h1 := mul_le_mul hC3 (mul_le_mul_of_nonneg_left hexp (sq_nonneg R)) hY hZ
          have h2 : 26 * (3 ^ d * (4 / (η / 2)) ^ 4) * R ^ 2 * (L ^ (-150 * η) * L ^ (2 * η) * L ^ γ * L ^ (η / 2)) =
              26 * ((3 ^ d * (4 / (η / 2)) ^ 4) * (R ^ 2 * (L ^ (-150 * η) * L ^ (2 * η) * L ^ γ * L ^ (η / 2)))) := by ring
          rw [h2]
          have h3 : 26 * (5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) * R ^ 2 * (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η)) =
              26 * ((5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) * (R ^ 2 * (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η)))) := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  · -- case B
    push Not at hρL
    have h3 : (2 * ρ * L + 1) ^ d ≤ 3 ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hRL : 1 ≤ R * L := by
      have := mul_le_mul_of_nonneg_right hRl hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this
    have hb1 : 8 * R * L ^ (2 * γ) + 5 ≤ 13 * L ^ (γ + η) := by
      have h1 : R * L ^ (2 * γ) ≤ L ^ (γ + η) := by
        calc R * L ^ (2 * γ) ≤ L ^ (-γ + η) * L ^ (2 * γ) :=
              mul_le_mul_of_nonneg_right hRu (Real.rpow_nonneg hL0.le _)
          _ = L ^ (γ + η) := by rw [← Real.rpow_add hL0]; congr 1; ring
      have h2 : 1 ≤ L ^ (γ + η) := Real.one_le_rpow hL1 (by linarith)
      have h3 : 8 * R * L ^ (2 * γ) = 8 * (R * L ^ (2 * γ)) := by ring
      linarith
    have hb2 : L ^ (-((d : ℝ) - γ)) ≤ L ^ (-(3 - γ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    have hmain : (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) *
        (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) ≤
        26 * 3 ^ d * (L ^ (γ + η) * L ^ (-(3 - γ))) * Real.log L ^ 4 := by
      have hBnn : 0 ≤ 2 * (8 * R * L ^ (2 * γ) + 5) := by positivity
      have hCnn : 0 ≤ L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4 := mul_nonneg (Real.rpow_nonneg hL0.le _) hlog0
      have hAB : (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) ≤ 3 ^ d * (2 * (13 * L ^ (γ + η))) :=
        mul_le_mul h3 (by linarith) hBnn (by positivity)
      have hC' : L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4 ≤ L ^ (-(3 - γ)) * Real.log L ^ 4 :=
        mul_le_mul_of_nonneg_right hb2 hlog0
      calc _ ≤ 3 ^ d * (2 * (13 * L ^ (γ + η))) * (L ^ (-(3 - γ)) * Real.log L ^ 4) :=
            mul_le_mul hAB hC' hCnn (by positivity)
        _ = _ := by ring
    refine hmain.trans ?_
    have h5 : (0 : ℝ) ≤ 26 * 3 ^ d * (L ^ (γ + η) * L ^ (-(3 - γ))) := by positivity
    have hR2 : L ^ (-2 : ℝ) ≤ R ^ 2 := by
      have h1 : L⁻¹ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hL0.le) hRl 2
      have h2 : L ^ (-2 : ℝ) = L⁻¹ ^ 2 := by
        rw [Real.rpow_neg hL0.le, inv_pow]; norm_cast
      rwa [h2]
    have hexp : L ^ (γ + η) * L ^ (-(3 - γ)) * L ^ ((1 - γ) / 2) ≤
        L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * L ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    calc 26 * 3 ^ d * (L ^ (γ + η) * L ^ (-(3 - γ))) * Real.log L ^ 4
        ≤ 26 * 3 ^ d * (L ^ (γ + η) * L ^ (-(3 - γ))) * ((4 / ((1 - γ) / 2)) ^ 4 * L ^ ((1 - γ) / 2)) :=
          mul_le_mul_of_nonneg_left hlog1 h5
      _ = 26 * (3 ^ d * (4 / ((1 - γ) / 2)) ^ 4) * (L ^ (γ + η) * L ^ (-(3 - γ)) * L ^ ((1 - γ) / 2)) := by ring
      _ ≤ 26 * (5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
            (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * L ^ (-2 : ℝ)) := by
          have hg : 0 < 1 - γ := by linarith
          have e : 4 / ((1 - γ) / 2) = 8 / (1 - γ) := by field_simp; ring
          have h8 : 0 ≤ (8 / η) ^ 4 := by positivity
          have h9 : 0 ≤ (8 / (1 - γ)) ^ 4 := by positivity
          have hC3 := const_le_b d h8 h9
          rw [e]
          have hY : 0 ≤ L ^ (γ + η) * L ^ (-(3 - γ)) * L ^ ((1 - γ) / 2) := by positivity
          have hW : 0 ≤ L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * L ^ (-2 : ℝ) := by positivity
          have hZ : 0 ≤ 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4) := by positivity
          have := mul_le_mul_of_nonneg_left (mul_le_mul hC3 hexp hY hZ) (by norm_num : (0:ℝ) ≤ 26)
          linarith
      _ ≤ 26 * (5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
            (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * R ^ 2) := by
          have hZ : 0 ≤ 26 * (5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) := by positivity
          have : L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * L ^ (-2 : ℝ) ≤
              L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η) * R ^ 2 :=
            mul_le_mul_of_nonneg_left hR2 (by positivity : (0:ℝ) ≤ L ^ (-η ^ 3) * L ^ (γ + 3 * η - 100 * η))
          exact mul_le_mul_of_nonneg_left this hZ
      _ = _ := by ring

end WaveTurbulence.FinalCount
