/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.AllCoupleDecay
public import WaveTurbulence.Foundations.IncohInst.TreeDecay
public import WaveTurbulence.Foundations.IncohInst.InputBounds

/-! # Small eta and coefficient enlargement for the exact parameter prefix -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh

theorem exists_source_eta0 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0 : ℝ) η₀,
      η ≤ 1 / 100 ∧ (100 * (d : ℝ)) ^ 2 * η ≤ 1 ∧ η < incoherenceExponent d γ := by
  have hg := incoherenceExponent_pos (by omega : 2 ≤ d) hγ
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : (0 : ℝ) < (100 * (d : ℝ)) ^ 2 := by positivity
  refine ⟨min (1 / 100) (min (1 / (100 * (d : ℝ)) ^ 2) (incoherenceExponent d γ / 2)),
    lt_min (by norm_num) (lt_min (div_pos zero_lt_one hc) (half_pos hg)), ?_⟩
  intro η hη
  have h₁ := hη.2.trans (min_le_left _ _)
  have h₂ := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h₁, ?_, lt_of_le_of_lt h₃ (half_lt_self hg)⟩
  have hh := (le_div_iff₀ hc).mp h₂
  simpa only [mul_comm] using hh

/-- Enlarge the already proved coefficient to the source's common `C₁`, retaining its outside factor. -/
theorem componentBound_le_regBound (P : WTParams) {C : ℝ} (hC : 0 ≤ C)
    (hCC : C ≤ P.C₁) (hC₁ : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    ENNReal.ofReal ((C * P.δ) ^ n *
      P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)) ≤ regBound P n g := by
  apply ENNReal.ofReal_le_ofReal
  change (C * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g) ≤
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)
  have hbase : 0 ≤ C * P.δ := mul_nonneg hC hδ
  have hp := pow_le_pow_left₀ hbase (mul_le_mul_of_nonneg_right hCC hδ) n
  have he := mul_le_mul_of_nonneg_right hC₁ (pow_nonneg (mul_nonneg (zero_le_one.trans hC₁) hδ) n)
  simp only [one_mul] at he
  exact mul_le_mul_of_nonneg_right (hp.trans he) (Real.rpow_nonneg hL _)

end WaveTurbulence.IncohInst
