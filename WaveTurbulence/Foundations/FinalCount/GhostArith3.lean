/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostArith2
/-! G2-GHOST part 6: the real inequalities, part 3: two blocks (one new `α`-atom, one ghost singleton). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem excessRHS_one (L γ η R : ℝ) (κ : ℕ) (hL : 0 < L) (ΔF ΔVβ : ℤ) :
    excessRHS L γ η [(R, κ)] ΔF ΔVβ =
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (ΔF : ℝ) - (min γ (1 - γ) + 2 * η ^ 2) * (ΔVβ : ℝ))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
  rw [excessRHS_split L γ η [(R, κ)] ΔF ΔVβ hL]
  simp

/-- The count `min(slab, box) · ball` of one `α`-gap, with the logarithms kept. -/
theorem lhs_ba (d : ℕ) {L γ η δ C₁ na R ρ : ℝ} (c κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R)) :
    (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
        Real.log L ^ 12 ≤
      3 * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hF := F1_bound d c hd hγ0 hγ1 hL hδ0 hδ hC hna0 hna
  have hA := atom_factor d κ hd hγ0 hγ1 hη hη1 hη2 hL hRl hRu hρ
  have hq0 := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hdq2 := delta_inv_qq_sq hδ0 hC
  rw [rankFactor_nat d L γ δ C₁ hL0 2]
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
  have hPc : 1 ≤ P ^ c := one_le_pow₀ (by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this)
  have hLm : 0 ≤ L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)) := by positivity
  calc F * B * ((L ^ (-((d : ℝ) - γ))) ^ 2 * qq δ C₁ ^ 2) * P ^ 12
      = (F * L ^ (-((d : ℝ) - γ)) * qq δ C₁) * (B * L ^ (-((d : ℝ) - γ))) * qq δ C₁ * P ^ 12 := by ring
    _ ≤ (3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * P ^ c * L ^ (min γ (1 - γ))) *
          (5 ^ d * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) * L ^ (-(3 * γ / 2 - η / 2))) * qq δ C₁ * P ^ 12 := by
        gcongr
    _ = (3 * 5 ^ d * 5 ^ d) * (δ⁻¹ * qq δ C₁ ^ 2) * P ^ (c + 12) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by ring
    _ ≤ (3 * 5 ^ d * 5 ^ d) * 1 * P ^ (c + 12) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        have h1 : (3 * 5 ^ d * 5 ^ d : ℝ) * (δ⁻¹ * qq δ C₁ ^ 2) ≤ (3 * 5 ^ d * 5 ^ d) * 1 :=
          mul_le_mul_of_nonneg_left hdq2 (by positivity)
        have hPp : 0 ≤ P ^ (c + 12) := by positivity
        have h2 := mul_le_mul_of_nonneg_right h1 hPp
        have h3 := mul_le_mul_of_nonneg_right h2 hLm
        have h4 := mul_le_mul_of_nonneg_right h3 hT
        exact h4
    _ = _ := by ring

/-- One new `α`-atom, one `β`-ghost: `ΔF = 0`, `ΔV_β = 0`. -/
theorem arith_B2_beta (d : ℕ) {L γ η δ C₁ na R ρ : ℝ} (c κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hH : 8 * η ≤ 2 * γ - 1)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R)) :
    (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
        Real.log L ^ 12 ≤
      (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * excessRHS L γ η [(R, κ)] 0 0 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have h1 := lhs_ba d c κ hd hγ0 hγ1 hη hη1 hη2 hL hδ0 hδ hC hna0 hna hRl hRu hρ
  refine h1.trans ?_
  rw [excessRHS_one L γ η R κ hL0]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  have hexp : L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((0 : ℤ)) : ℝ))) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have h1 : min γ (1 - γ) ≤ 1 - γ := min_le_right _ _
    push_cast
    have : η ^ 2 ≤ η := by nlinarith
    have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
    linarith
  have hLm : 0 ≤ L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)) := by positivity
  calc 3 * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)
      ≤ 3 * 5 ^ d * 5 ^ d * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        gcongr
    _ = (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
          ((L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hT) (by positivity)

/-- One new `α`-atom, one `α`-ghost (label `Q_g`, `κ_g`): `ΔF = 0`, `ΔV_β = 1`, charge `T(Q_g, κ_g)⁻¹`. -/
theorem arith_B2_alpha (d : ℕ) {L γ η δ C₁ na R ρ Qg : ℝ} (c κ κg : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hH : 8 * η ≤ 2 * γ - 1)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hQl : L⁻¹ ≤ Qg) (hQu : Qg ≤ L ^ (-γ + η)) :
    (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
        Real.log L ^ 12 ≤
      (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [(R, κ)] 0 1 / (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hQ0 : 0 < Qg := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have h1 := lhs_ba d c κ hd hγ0 hγ1 hη hη1 hη2 hL hδ0 hδ hC hna0 hna hRl hRu hρ
  refine h1.trans ?_
  rw [excessRHS_one L γ η R κ hL0]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  have hTg : 0 < L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg := by positivity
  have hLm : 0 ≤ L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)) := by positivity
  have hg0 : min γ (1 - γ) ≤ 1 - γ := min_le_right _ _
  have hK : 0 ≤ 3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have hkg : (0 : ℝ) ≤ (κg : ℝ) * η := by positivity
  have hmain : (L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) * (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((1 : ℤ)) : ℝ))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
    have hX : (L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
        (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) ≤
        L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
          (min γ (1 - γ) + 2 * η ^ 2) * (((1 : ℤ)) : ℝ))) := by
      calc (L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
            (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)
          ≤ (L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
            (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * L ^ (-γ + η)) := by gcongr
        _ = L ^ (η ^ 2 + (min γ (1 - γ) + -(3 * γ / 2 - η / 2)) + (((γ + 3 * η) / 2 - (κg : ℝ) * η) + (-γ + η))) := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
        _ ≤ _ := by
            apply Real.rpow_le_rpow_of_exponent_le hL1
            push_cast
            have : η ^ 2 ≤ η := by nlinarith
            have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
            linarith
    calc _ = (L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
            (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) *
            (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hX hT
  calc 3 * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)
      ≤ 3 * 5 ^ d * 5 ^ d * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        gcongr
    _ = (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
          ((L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)) := by ring
    _ ≤ (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
          ((L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((1 : ℤ)) : ℝ))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)) /
          (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        rw [le_div_iff₀ hTg]
        exact hmain

end WaveTurbulence.FinalCount
