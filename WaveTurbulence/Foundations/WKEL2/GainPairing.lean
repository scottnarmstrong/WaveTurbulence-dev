/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainDiagonalShift
public import WaveTurbulence.Foundations.WKEL2.GainCauchyAlgebra

/-!
# The unweighted gain Schur pairing

Research-note Proposition 7a, with two unweighted L² slots and two weighted
L² slots. The resonant measure here omits the delta factor one half.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The gain pairing bound follows from the two first-loss diagonals by Cauchy–Schwarz. -/
theorem exists_gain_pairing_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ F₁ f₂ f₃ F₄ : Mom d → ℝ,
      Measurable F₁ → Measurable f₂ → Measurable f₃ → Measurable F₄ →
      MemLp F₁ 2 → MemLp (weightedFunction s f₂) 2 → MemLp (weightedFunction s f₃) 2 → MemLp F₄ 2 →
      (∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal |F₁ (q.1 + q.2.1)| *
        ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |f₃ (q.1 + q.2.2)| *
          ENNReal.ofReal |F₄ q.1| ∂volume.prod (resonantMeasure e)) ≤
        (ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₂ * weightedL2Norm s f₃)) *
          ENNReal.ofReal (weightedL2Norm 0 F₁ * weightedL2Norm 0 F₄) := by
  obtain ⟨C, hC, hb⟩ := exists_gain_diagonal_bound hd s hs
  refine ⟨C, hC, fun e he F₁ f₂ f₃ F₄ h₁ h₂ h₃ h₄ hL₁ hL₂ hL₃ hL₄ => ?_⟩
  let μ := (volume : Measure (Mom d)).prod (resonantMeasure e)
  let U : Mom d × (Mom d × Mom d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| * ENNReal.ofReal |f₃ (q.1 + q.2.2)|
  let L : Mom d × (Mom d × Mom d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal |F₁ (q.1 + q.2.1)| * U q ^ ((1 : ℝ) / 2)
  let R : Mom d × (Mom d × Mom d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal |F₄ q.1| * U q ^ ((1 : ℝ) / 2)
  have hU : Measurable U :=
    (h₂.abs.ennreal_ofReal.comp (by fun_prop)).mul (h₃.abs.ennreal_ofReal.comp (by fun_prop))
  have hL : Measurable L :=
    (h₁.abs.ennreal_ofReal.comp (by fun_prop)).mul (hU.pow_const ((1 : ℝ) / 2))
  have hR : Measurable R :=
    (h₄.abs.ennreal_ofReal.comp measurable_fst).mul (hU.pow_const ((1 : ℝ) / 2))
  have hprod (q : Mom d × (Mom d × Mom d)) : (L * R) q =
      ENNReal.ofReal |F₁ (q.1 + q.2.1)| * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
        ENNReal.ofReal |f₃ (q.1 + q.2.2)| * ENNReal.ofReal |F₄ q.1| := by
    dsimp only [L, R, Pi.mul_apply]
    rw [ennreal_gain_factor_product]
    dsimp only [U]
    ac_rfl
  have hLsq (q : Mom d × (Mom d × Mom d)) : L q ^ (2 : ℝ) =
      ENNReal.ofReal ((F₁ (q.1 + q.2.1)) ^ 2) * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
        ENNReal.ofReal |f₃ (q.1 + q.2.2)| := by
    dsimp only [L]
    rw [ENNReal.rpow_two, ennreal_gain_factor_sq, ennreal_ofReal_abs_sq]
    exact (mul_assoc _ _ _).symm
  have hRsq (q : Mom d × (Mom d × Mom d)) : R q ^ (2 : ℝ) =
      ENNReal.ofReal ((F₄ q.1) ^ 2) * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
        ENNReal.ofReal |f₃ (q.1 + q.2.2)| := by
    dsimp only [R]
    rw [ENNReal.rpow_two, ennreal_gain_factor_sq, ennreal_ofReal_abs_sq]
    exact (mul_assoc _ _ _).symm
  have hLb : (∫⁻ q, L q ^ (2 : ℝ) ∂μ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₂ * weightedL2Norm s f₃)) *
        ENNReal.ofReal ((weightedL2Norm 0 F₁) ^ 2) := by
    simp_rw [hLsq]
    rw [lintegral_gain_diagonal_shift he (by omega) h₁ h₂ h₃]
    simpa only [mul_comm (weightedL2Norm s f₃) (weightedL2Norm s f₂)] using
      hb e he F₁ f₃ f₂ h₁ h₃ h₂ hL₁ hL₃ hL₂
  have hRb : (∫⁻ q, R q ^ (2 : ℝ) ∂μ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₂ * weightedL2Norm s f₃)) *
        ENNReal.ofReal ((weightedL2Norm 0 F₄) ^ 2) := by
    simp_rw [hRsq]
    exact hb e he F₄ f₂ f₃ h₄ h₂ h₃ hL₄ hL₂ hL₃
  have hconj : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hL.aemeasurable hR.aemeasurable
  simp_rw [hprod] at hHolder
  calc
    _ ≤ _ := hHolder
    _ ≤ ((ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₂ * weightedL2Norm s f₃)) *
          ENNReal.ofReal ((weightedL2Norm 0 F₁) ^ 2)) ^ ((1 : ℝ) / 2) *
        ((ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₂ * weightedL2Norm s f₃)) *
          ENNReal.ofReal ((weightedL2Norm 0 F₄) ^ 2)) ^ ((1 : ℝ) / 2) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hLb (by norm_num))
        (ENNReal.rpow_le_rpow hRb (by norm_num))
    _ = _ := ennreal_schur_norm_constant _ _ _ (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _)

end WaveTurbulence.WKEL2
