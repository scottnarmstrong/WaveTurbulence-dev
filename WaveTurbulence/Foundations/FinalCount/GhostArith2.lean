/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostArith1
/-! G2-GHOST part 5: the real inequalities, part 2: the partition `{0|1|2}` (three singleton blocks). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem excessRHS_nil (L γ η : ℝ) (hL : 0 < L) (ΔF ΔVβ : ℤ) :
    excessRHS L γ η [] ΔF ΔVβ =
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (ΔF : ℝ) - (min γ (1 - γ) + 2 * η ^ 2) * (ΔVβ : ℝ))) := by
  rw [excessRHS_split L γ η [] ΔF ΔVβ hL]
  simp

/-- `{0|1|2}` with only `β`-ghosts (`g` of them): the count is `min(slab, box)`. -/
theorem arith_P5_beta (d : ℕ) {L γ η δ C₁ na : ℝ} (c g : ℕ) (hg : g ≤ 3) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) :
    ((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12)) *
        excessRHS L γ η [] (2 - (g : ℤ)) (3 - 2 * (g : ℤ)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hF := F1_bound d c hd hγ0 hγ1 hL hδ0 hδ hC hna0 hna
  rw [rankFactor_nat d L γ δ C₁ hL0 1, excessRHS_nil L γ η hL0]
  simp only [pow_one]
  have hlog := log_pow_le (c + 12) (by omega) L (η ^ 2 / 2) hL1 (by positivity)
  have hP0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hdq := delta_inv_qq (C₁ := C₁) hδ0 hC
  have hK0 : 0 ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) := by
    have := qq_nonneg hδ0.le (zero_le_one.trans hC); positivity
  have hexp : L ^ (min γ (1 - γ)) * L ^ (η ^ 2 / 2) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((2 - (g : ℤ) : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((3 - 2 * (g : ℤ) : ℤ)) : ℝ))) := by
    rw [← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    have hg' : (g : ℝ) ≤ 3 := by exact_mod_cast hg
    have h3 : η ^ 3 ≤ η ^ 2 / 2 := by
      have hη2 : η ≤ 1 / 2 := by linarith
      calc η ^ 3 = η ^ 2 * η := by ring
        _ ≤ η ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hη2 (sq_nonneg η)
        _ = η ^ 2 / 2 := by ring
    linarith [mul_nonneg (sq_nonneg η) (by linarith : (0:ℝ) ≤ 3 - (g : ℝ))]
  calc _ = (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * L ^ (-((d : ℝ) - γ)) * qq δ C₁) * Real.log L ^ 12 := by ring
    _ ≤ (3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (min γ (1 - γ))) * Real.log L ^ 12 :=
        mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ (c + 12) * L ^ (min γ (1 - γ)) := by ring
    _ ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) * L ^ (η ^ 2 / 2) * L ^ (min γ (1 - γ)) := by
        have := mul_le_mul_of_nonneg_left hlog hK0
        have hLg : 0 ≤ L ^ (min γ (1 - γ)) := Real.rpow_nonneg hL0.le _
        linarith [mul_le_mul_of_nonneg_right this hLg]
    _ ≤ (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12)) *
          L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((2 - (g : ℤ) : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((3 - 2 * (g : ℤ) : ℤ)) : ℝ))) := by
        have hcoef : 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) ≤ 3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) := by
          have : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
          exact mul_le_mul_of_nonneg_left hdq this
        have hm : 0 ≤ (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) := by positivity
        calc 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) * L ^ (η ^ 2 / 2) * L ^ (min γ (1 - γ)) =
            (3 * 5 ^ d * (δ⁻¹ * qq δ C₁)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (η ^ 2 / 2)) := by ring
          _ ≤ (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ))) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) *
              L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((2 - (g : ℤ) : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((3 - 2 * (g : ℤ) : ℤ)) : ℝ))) := by gcongr
          _ = _ := by ring

/-- The `ν`-slab term with the logarithms absorbed. -/
theorem lhs_nu (d : ℕ) {L γ η δ C₁ na Q ρ : ℝ} (c : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQl : L⁻¹ ≤ Q) (hQu : Q ≤ L ^ (-γ + η)) (hρ : ρ = Q / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (L ^ (η ^ 2) * (L ^ (-γ) / Q)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have hF := Fnu_bound d c hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQl hQu hρ
  rw [rankFactor_nat d L γ δ C₁ hL0 1]
  simp only [pow_one]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hP0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hdq := delta_inv_qq (C₁ := C₁) hδ0 hC
  have hK : 0 ≤ L ^ (-γ) / Q := by positivity
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hK0 : 0 ≤ 9 * (d : ℝ) * 5 ^ d * (δ⁻¹ * qq δ C₁) := by
    have := qq_nonneg hδ0.le (zero_le_one.trans hC); positivity
  calc _ = (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        L ^ (-((d : ℝ) - γ)) * qq δ C₁ * Real.log L ^ 12 := by ring
    _ ≤ (9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * (L ^ (-γ) / Q)) * Real.log L ^ 12 :=
        mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ (c + 12) * (L ^ (-γ) / Q) := by ring
    _ ≤ 9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) * (L ^ (-γ) / Q) := by
        gcongr
    _ ≤ (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (L ^ (η ^ 2) * (L ^ (-γ) / Q)) := by
        have hm : 0 ≤ (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
        have hLe : 0 ≤ L ^ (η ^ 2) * (L ^ (-γ) / Q) := by positivity
        calc 9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) * (L ^ (-γ) / Q)
            = (9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * (L ^ (η ^ 2) * (L ^ (-γ) / Q)) := by ring
          _ ≤ (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ))) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * (L ^ (η ^ 2) * (L ^ (-γ) / Q)) := by
              have h9 : 9 * (d : ℝ) * 5 ^ d * (δ⁻¹ * qq δ C₁) ≤ 9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hdq (by positivity)
              gcongr
          _ = _ := by ring

/-- `{0|1|2}` with one `α`-ghost (label `Q`, `κ`) and `gb ≤ 2` `β`-ghosts. -/
theorem arith_P5_alpha1 (d : ℕ) {L γ η δ C₁ na Q ρ : ℝ} (c κ gb : ℕ) (hgb : gb ≤ 2) (hd : 3 ≤ d) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQl : L⁻¹ ≤ Q)
    (hQu : Q ≤ L ^ (-γ + η)) (hρ : ρ = Q / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (1 - (gb : ℤ)) (2 - 2 * (gb : ℤ)) /
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * Q)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have h1 := lhs_nu d c hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQl hQu hρ
  rw [excessRHS_nil L γ η hL0]
  refine h1.trans ?_
  have hT : 0 < L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * Q := by positivity
  have hK0 : 0 ≤ 9 * (d : ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [le_div_iff₀ hT]
  have hE : -η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((1 - (gb : ℤ) : ℤ)) : ℝ) -
      (min γ (1 - γ) + 2 * η ^ 2) * (((2 - 2 * (gb : ℤ) : ℤ)) : ℝ)) = -η ^ 3 + η ^ 2 * (1 - (gb : ℝ)) := by
    push_cast; ring
  rw [hE]
  calc L ^ (η ^ 2) * (L ^ (-γ) / Q) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * Q)
      = L ^ (η ^ 2) * L ^ (-γ) * L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) := by field_simp
    _ = L ^ (η ^ 2 + -γ + ((γ + 3 * η) / 2 - (κ : ℝ) * η)) := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0]
    _ ≤ L ^ (-η ^ 3 + η ^ 2 * (1 - (gb : ℝ))) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        have hg : (gb : ℝ) ≤ 2 := by exact_mod_cast hgb
        have hk : (0 : ℝ) ≤ (κ : ℝ) * η := by positivity
        have hηle : η ≤ 1 := by linarith
        have h3 : η ^ 3 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le hηle (by norm_num)
        have h4 : η ^ 2 ≤ η := pow_le_of_le_one hη.le hηle (by norm_num)
        linarith [mul_nonneg (sq_nonneg η) (by linarith : (0:ℝ) ≤ 2 - (gb : ℝ))]

/-- `{0|1|2}` with two `α`-ghosts (labels `Q₁, Q₂`) and `gb ≤ 1` `β`-ghosts; the slab is that of `Q₂`.
Needs `8η ≤ 2γ - 1` (the group D of the research notes). -/
theorem arith_P5_alpha2 (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ ρ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ)
    (hH : 8 * η ≤ 2 * γ - 1) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₁u : Q₁ ≤ L ^ (-γ + η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) (hρ : ρ = Q₂ / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ₁0 : 0 < Q₁ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₁l
  have hQ₂0 : 0 < Q₂ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₂l
  have h1 := lhs_nu d c hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQ₂l hQ₂u hρ
  rw [excessRHS_nil L γ η hL0]
  refine h1.trans ?_
  have hT : 0 < (L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂) := by positivity
  have hK0 : 0 ≤ 9 * (d : ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [le_div_iff₀ hT]
  have hg0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith)
  have hE : -η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((-(gb : ℤ) : ℤ)) : ℝ) -
      (min γ (1 - γ) + 2 * η ^ 2) * (((1 - 2 * (gb : ℤ) : ℤ)) : ℝ)) =
        -η ^ 3 - (1 - γ) - 2 * η ^ 2 - (gb : ℝ) * η ^ 2 := by
    rw [hg0]; push_cast; ring
  rw [hE]
  have hk1 : (0 : ℝ) ≤ (κ₁ : ℝ) * η := by positivity
  have hk2 : (0 : ℝ) ≤ (κ₂ : ℝ) * η := by positivity
  have hu1 : L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) ≤ L ^ (γ + 3 * η) := by
    rw [← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    linarith
  calc L ^ (η ^ 2) * (L ^ (-γ) / Q₂) * ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) *
        (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))
      = L ^ (η ^ 2) * L ^ (-γ) * (L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η)) * Q₁ := by
        field_simp
    _ ≤ L ^ (η ^ 2) * L ^ (-γ) * L ^ (γ + 3 * η) * L ^ (-γ + η) := by
        have hp : 0 ≤ L ^ (η ^ 2) * L ^ (-γ) := by positivity
        gcongr
    _ = L ^ (η ^ 2 + -γ + (γ + 3 * η) + (-γ + η)) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    _ ≤ L ^ (-η ^ 3 - (1 - γ) - 2 * η ^ 2 - (gb : ℝ) * η ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        have hg : (gb : ℝ) ≤ 1 := by exact_mod_cast hgb
        have hηle : η ≤ 1 / 2 := by linarith only [hη1, hγ1]
        have h3 : η ^ 3 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le (by linarith) (by norm_num)
        have h4 : η ^ 2 ≤ η / 2 := by
          calc η ^ 2 = η * η := sq η
            _ ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left hηle hη.le
            _ = η / 2 := by ring
        linarith [mul_nonneg (sq_nonneg η) (by linarith : (0:ℝ) ≤ 1 - (gb : ℝ))]

end WaveTurbulence.FinalCount
