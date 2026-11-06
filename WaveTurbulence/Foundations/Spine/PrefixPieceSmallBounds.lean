/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import WaveTurbulence.Foundations.Spine.FinalNumerics
import Mathlib.Tactic
/-! Threshold lemmas for the numerical constraints of `PieceSmall`: `delta` small (after `eta`, `nu`, `C_1`)
and `L` large (after `eta`, `gamma`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Filter Set

theorem exists_delta_piece_threshold {η ν C₁ K : ℝ} (hη : 0 < η) (hν : 0 < ν) (hC₁ : 1 ≤ C₁)
    (hK : 0 < K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) δ₀, δ ≤ 1 ∧ δ ^ (5 * ν) ≤ η ^ 6 ∧
      Real.log C₁ + Real.log K + 5 * ν * Real.log δ ≤ 0 := by
  refine ⟨min 1 (min (Real.exp (6 * Real.log η / (5 * ν)))
    (Real.exp (-(Real.log C₁ + Real.log K) / (5 * ν)))), by positivity, ?_⟩
  intro δ hδ
  have h1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have h2 : δ ≤ Real.exp (6 * Real.log η / (5 * ν)) :=
    hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : δ ≤ Real.exp (-(Real.log C₁ + Real.log K) / (5 * ν)) :=
    hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlog2 : Real.log δ ≤ 6 * Real.log η / (5 * ν) := by
    have := Real.log_le_log hδ.1 h2
    rwa [Real.log_exp] at this
  have hlog3 : Real.log δ ≤ -(Real.log C₁ + Real.log K) / (5 * ν) := by
    have := Real.log_le_log hδ.1 h3
    rwa [Real.log_exp] at this
  have h5ν : 0 < 5 * ν := by positivity
  refine ⟨h1, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hδ.1]
    have : η ^ 6 = Real.exp (6 * Real.log η) := by
      rw [show (6 : ℝ) * Real.log η = (6 : ℕ) * Real.log η by norm_num, Real.exp_nat_mul,
        Real.exp_log hη]
    rw [this]
    apply Real.exp_le_exp.mpr
    have := (le_div_iff₀ h5ν).mp (by linarith : Real.log δ ≤ 6 * Real.log η / (5 * ν))
    nlinarith
  · have := (le_div_iff₀ h5ν).mp hlog3
    nlinarith

theorem eventually_L_piece_small {η γ : ℝ} (hη : 0 < η) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hηγ : η ≤ γ / 2) (hη1 : η ≤ (1 - γ) / 2) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      2 * L⁻¹ ≤ L ^ (-γ + η) ∧ L ^ (-γ + η) ≤ 1 ∧
      Real.log (Real.log L / Real.log 2 + 2) ≤ η ^ 6 * Real.log L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- scale_log threshold
  set ε : ℝ := η ^ 6 * Real.log 2 / 4 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.mp (eventually_log_le_mul hε0)
  have h1γ : 0 < 1 - γ := by linarith [hγ.2]
  set M : ℝ := max (max ℓ₁ 1) (Real.log 2 / (1 - γ)) with hM
  have hM1 : 1 ≤ M := (le_max_right ℓ₁ 1).trans (le_max_left _ _)
  refine ⟨Real.exp M, ?_, ?_⟩
  · calc (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
      _ ≤ Real.exp M := Real.exp_le_exp.mpr hM1
  intro L hL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hℓ : M ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hL
    rwa [Real.log_exp] at this
  set ℓ : ℝ := Real.log L with hℓdef
  have hℓ1 : 1 ≤ ℓ := hM1.trans hℓ
  have hL1 : 1 ≤ L := by
    rw [hℓdef] at hℓ1
    by_contra h
    have := Real.log_neg hL0 (by linarith)
    linarith
  have hLexp : ∀ x : ℝ, L ^ x = Real.exp (x * ℓ) := fun x => by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · -- 2 / L <= L^(-γ+η)
    have hℓ2 : Real.log 2 / (1 - γ) ≤ ℓ := (le_max_right _ _).trans hℓ
    have h2 : (2 : ℝ) ≤ L ^ (1 - γ + η) := by
      rw [hLexp]
      have : Real.log 2 ≤ (1 - γ + η) * ℓ := by
        have h3 := (div_le_iff₀ h1γ).mp hℓ2
        nlinarith [mul_nonneg hη.le (by linarith : (0 : ℝ) ≤ ℓ)]
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.mpr this
    have h4 : L ^ (1 - γ + η) = L ^ (-γ + η) * L := by
      rw [show 1 - γ + η = (-γ + η) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    rw [h4] at h2
    rw [inv_eq_one_div, ← mul_div_assoc, mul_one, div_le_iff₀ hL0]
    exact h2
  · exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  · have hx : ℓ₁ ≤ ℓ / Real.log 2 + 2 := by
      have hl2' : Real.log 2 < 1 :=
        (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by
          have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith)
      have : ℓ ≤ ℓ / Real.log 2 := by
        rw [le_div_iff₀ hl2]; nlinarith
      have hℓ₁ℓ : ℓ₁ ≤ ℓ := (le_max_left _ _).trans ((le_max_left _ _).trans hℓ)
      linarith
    have h := hℓ₁ _ hx
    have : ε * (ℓ / Real.log 2 + 2) ≤ η ^ 6 * ℓ := by
      rw [hε]
      have hl2' : Real.log 2 < 1 :=
        (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by
          have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith)
      have h6 : 0 < η ^ 6 := by positivity
      have : η ^ 6 * Real.log 2 / 4 * (ℓ / Real.log 2 + 2) = η ^ 6 * ℓ / 4 + η ^ 6 * Real.log 2 / 2 := by
        field_simp; ring
      rw [this]
      nlinarith [mul_pos h6 hl2]
    linarith


theorem exists_delta_absorb_threshold {ν C₀ C₁ : ℝ} (hν : 0 < ν) (hC₀ : 1 ≤ C₀) (hC₁ : 1 ≤ C₁) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) δ₀, C₀ * C₁ * δ ^ (2 * ν) ≤ 1 := by
  have hK : 0 < C₀ * C₁ := by positivity
  refine ⟨Real.exp (-(Real.log (C₀ * C₁)) / (2 * ν)), Real.exp_pos _, ?_⟩
  intro δ hδ
  have hlog : Real.log δ ≤ -(Real.log (C₀ * C₁)) / (2 * ν) := by
    have := Real.log_le_log hδ.1 hδ.2
    rwa [Real.log_exp] at this
  have h2ν : 0 < 2 * ν := by positivity
  have h := (le_div_iff₀ h2ν).mp hlog
  rw [Real.rpow_def_of_pos hδ.1]
  have : C₀ * C₁ * Real.exp (Real.log δ * (2 * ν)) ≤ 1 := by
    have e : C₀ * C₁ = Real.exp (Real.log (C₀ * C₁)) := (Real.exp_log hK).symm
    rw [e, ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    nlinarith
  exact this

end WaveTurbulence.LGSpine
