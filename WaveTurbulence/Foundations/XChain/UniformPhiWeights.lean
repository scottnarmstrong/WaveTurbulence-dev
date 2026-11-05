/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.UniformSchwartzBracket
public import WaveTurbulence.Foundations.XChain.StageSizeThreshold
/-! One compact-time Schwartz bound supplies every stage's source momentum weight. -/
public section
namespace WaveTurbulence.Induct
open Set

theorem uniform_phi_stage_weight (P : WTParams) (hd : 1 ≤ P.d) (hδ : 0 ≤ P.δ)
    (htime : P.δ * P.D ≤ P.τstar) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ t ∈ Icc 0 P.τstar, ∀ k,
      |P.φ t k| ≤ B * jbr k ^ (-(4 * P.Lambda 0 : ℝ)))
    {q : ℕ} (hq : q ≤ P.D) {t : ℝ} (ht : t ∈ Icc 0 (q : ℝ)) :
    ∀ k, |P.φ (P.δ * t) k| ≤ B * jbr k ^ (-(4 * P.Lambda q : ℝ)) := by
  have hq' : (q : ℝ) ≤ P.D := by exact_mod_cast hq
  have hdt : P.δ * t ∈ Icc 0 P.τstar :=
    ⟨mul_nonneg hδ ht.1, (mul_le_mul_of_nonneg_left (ht.2.trans hq') hδ).trans htime⟩
  intro k
  apply (hφ _ hdt k).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr k)
  have hΛ : (P.Lambda q : ℝ) ≤ P.Lambda 0 := by exact_mod_cast lambda_le_zero P hd q
  linarith

theorem phi_stage_input_weight (P : WTParams) (q : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k, |P.φ (P.δ * q) k| ≤ B * jbr k ^ (-(4 * P.Lambda q : ℝ))) :
    ∀ k, |P.φ (P.δ * q) k| ≤ B * jbr k ^ (-(P.Lambda q : ℝ)) := by
  intro k
  apply (hφ k).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr k)
  have hΛ : (0 : ℝ) ≤ P.Lambda q := Nat.cast_nonneg _
  linarith

end WaveTurbulence.Induct
