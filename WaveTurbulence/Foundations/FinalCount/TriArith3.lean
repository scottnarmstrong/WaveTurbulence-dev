/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriArith2
/-! Triangles, part 18 (FINALCOUNT-G2): the three arithmetic cases of DH23 L1793--L1796. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem excessRHS_split (L γ η : ℝ) (αs : List (ℝ × ℕ)) (ΔF ΔVβ : ℤ) (hL : 0 < L) :
    excessRHS L γ η αs ΔF ΔVβ =
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (ΔF : ℝ) - (min γ (1 - γ) + 2 * η ^ 2) * (ΔVβ : ℝ))) *
        (αs.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod := by
  unfold excessRHS
  rw [Real.rpow_add hL]; ring

theorem excessRHS_bb (L γ η : ℝ) (hL : 0 < L) :
    excessRHS L γ η [] 2 3 = L ^ (-η ^ 3 + (min γ (1 - γ) + 4 * η ^ 2)) := by
  rw [excessRHS_split L γ η [] 2 3 hL]
  simp only [List.map_nil, List.prod_nil, mul_one]
  congr 1; push_cast; ring

theorem excessRHS_ba (L γ η R : ℝ) (κ : ℕ) (hL : 0 < L) :
    excessRHS L γ η [(R, κ)] 1 2 = L ^ (-η ^ 3 + η ^ 2) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
  rw [excessRHS_split L γ η _ 1 2 hL]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2; push_cast; ring

theorem excessRHS_aa (L γ η R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hL : 0 < L) :
    excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1 = L ^ (-η ^ 3 - (min γ (1 - γ) + 2 * η ^ 2)) *
      ((L ^ ((γ + 3 * η) / 2 - (κ₀ : ℝ) * η) * R₀) * (L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * R₁)) := by
  rw [excessRHS_split L γ η _ 0 1 hL]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2; push_cast; ring

/-- A power of the logarithm is at most a constant times `L^{η²}`. -/
theorem log_pow_le_eta (m : ℕ) (hm : 0 < m) {L η : ℝ} (hL : 1 ≤ L) (hη : 0 < η) :
    Real.log L ^ m ≤ ((m : ℝ) / η ^ 2) ^ m * L ^ (η ^ 2) :=
  log_pow_le m hm L (η ^ 2) hL (by positivity)

/-- **`ΔF = 2`.** -/
theorem arith_bb (d : ℕ) {L γ η δ C₁ na : ℝ} (c : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) :
    ((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * excessRHS L γ η [] 2 3 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hF := F1_bound d c hd hγ0 hγ1 hL hδ0 hδ hC hna0 hna
  rw [rankFactor_nat d L γ δ C₁ hL0 1, excessRHS_bb L γ η hL0]
  simp only [pow_one]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hP0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hdq := delta_inv_qq (C₁ := C₁) hδ0 hC
  have hK0 : 0 ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) := by
    have := qq_nonneg hδ0.le (zero_le_one.trans hC); positivity
  have hexp : L ^ (min γ (1 - γ)) * L ^ (η ^ 2) ≤ L ^ (-η ^ 3 + (min γ (1 - γ) + 4 * η ^ 2)) := by
    rw [← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have : η ^ 3 ≤ η ^ 2 := by nlinarith [sq_nonneg η]
    nlinarith
  calc _ = (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * L ^ (-((d : ℝ) - γ)) * qq δ C₁) * Real.log L ^ 12 := by ring
    _ ≤ (3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (min γ (1 - γ))) * Real.log L ^ 12 :=
        mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ (c + 12) * L ^ (min γ (1 - γ)) := by ring
    _ ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2) * L ^ (min γ (1 - γ)) := by
        have := mul_le_mul_of_nonneg_left hlog hK0
        have hLg : 0 ≤ L ^ (min γ (1 - γ)) := Real.rpow_nonneg hL0.le _
        nlinarith [mul_le_mul_of_nonneg_right this hLg]
    _ ≤ (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * L ^ (-η ^ 3 + (min γ (1 - γ) + 4 * η ^ 2)) := by
        have hcoef : 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) ≤ 3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) := by
          have : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
          exact mul_le_mul_of_nonneg_left hdq this
        have hm : 0 ≤ (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
        have hLp : 0 ≤ L ^ (min γ (1 - γ)) * L ^ (η ^ 2) := by positivity
        calc 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2) * L ^ (min γ (1 - γ)) =
            (3 * 5 ^ d * (δ⁻¹ * qq δ C₁)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (η ^ 2)) := by ring
          _ ≤ (3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ))) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (-η ^ 3 + (min γ (1 - γ) + 4 * η ^ 2)) := by
              gcongr
          _ = _ := by ring

end WaveTurbulence.FinalCount
