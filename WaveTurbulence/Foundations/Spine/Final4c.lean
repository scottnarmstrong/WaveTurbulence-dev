/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final4b
import Mathlib.Tactic
/-! The spine gate `WTPrefix LadderFourierAt`. -/
@[expose] public section
open Filter Topology Finset
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine

/-- The constant `C₁`. -/
noncomputable def C1star (d : ℕ) : ℝ := 128 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1)))

theorem one_le_C1star {d : ℕ} (hd : 1 ≤ d) : 1 ≤ C1star d := by
  unfold C1star
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have : (0 : ℝ) ≤ d * (2 : ℝ) ^ (d - 1) := by positivity
  nlinarith

theorem delta_small {τ ν δ : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 / (2 * τ)) ^ (1 / (5 * ν))) : τ * δ ^ (5 * ν) ≤ 1 / 2 := by
  have h1 : δ ^ (5 * ν) ≤ ((1 / (2 * τ)) ^ (1 / (5 * ν))) ^ (5 * ν) :=
    Real.rpow_le_rpow hδ0.le hδ (by positivity)
  rw [← Real.rpow_mul (by positivity)] at h1
  have : 1 / (5 * ν) * (5 * ν) = 1 := by field_simp
  rw [this, Real.rpow_one] at h1
  calc τ * δ ^ (5 * ν) ≤ τ * (1 / (2 * τ)) := by gcongr
    _ = 1 / 2 := by field_simp

theorem eventually_conditions (d : ℕ) (γ δ ν : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (_hν : 0 < ν) :
    ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧ 20 ≤ Real.log L ∧ Real.log L ^ 2 < 1 + δ * L ^ (2 * γ) ∧
      (Real.log L) ^ (2 * d + 4) ≤ L ^ (δ ^ (5 * ν) / 2) ∧ (Real.log L) ^ 2 ≤ L ^ (δ ^ (5 * ν)) ∧
      128 * (180 * d * Real.log L) ≤ L ^ (δ ^ (5 * ν)) := by
  have hs : 0 < δ ^ (5 * ν) := Real.rpow_pos_of_pos hδ _
  filter_upwards [eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 20,
    eventually_log_pow_le 2 (1 / δ) (2 * γ) (by positivity) (by positivity),
    eventually_log_pow_le (2 * d + 4) 1 (δ ^ (5 * ν) / 2) (by norm_num) (by positivity),
    eventually_log_pow_le 2 1 (δ ^ (5 * ν)) (by norm_num) hs,
    eventually_log_pow_le 1 (128 * 180 * d) (δ ^ (5 * ν)) (by positivity) hs]
    with L h3 h20 h2 h4 h5 h6
  refine ⟨h3, h20, ?_, by simpa using h4, by simpa using h5, ?_⟩
  · have : (Real.log L) ^ 2 ≤ δ * L ^ (2 * γ) := by
      have := mul_le_mul_of_nonneg_left h2 hδ.le
      calc (Real.log L) ^ 2 = δ * (1 / δ * (Real.log L) ^ 2) := by field_simp
        _ ≤ δ * L ^ (2 * γ) := this
    linarith
  · calc 128 * (180 * d * Real.log L) = 128 * 180 * d * (Real.log L) ^ 1 := by ring
      _ ≤ _ := h6

theorem ladderFourier_prefix : WTPrefix LadderFourierAt := by
  intro d hd γ hγ
  refine ⟨1, one_pos, fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  have hd1 : 1 ≤ d := by omega
  refine ⟨C1star d, one_le_C1star hd1, 1, one_pos, fun ν hν => ?_⟩
  have hν0 : 0 < ν := hν.1
  refine ⟨min 1 ((1 / (2 * τstar)) ^ (1 / (5 * ν))), by have := hτ; have := hν0; positivity,
    fun δ hδ D hD hτD => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hsmall := delta_small hτ hν0 hδ0 (hδ.2.trans (min_le_right _ _))
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp (eventually_conditions d γ δ ν hγ.1 hδ0 hν0)
  refine ⟨1, le_rfl, max L1 2, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨h3, h20, hbig, hlog, hΛLam, hfree⟩ := hL1 L (le_trans (le_max_left _ _) hL)
  have hLpos : 0 < L := by linarith
  have hs : 0 < δ ^ (5 * ν) := Real.rpow_pos_of_pos hδ0 _
  apply ladder_fourier_param
  refine ⟨hd1, hLpos, hδ0, hδ1, hν0.le, by linarith, hbig, Y_bound (by linarith) h20 hd1, ?_, hΛLam, hfree,
    le_refl _, one_le_C1star hd1⟩
  -- the exponential estimate
  show Real.exp ((D : ℝ) * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ L ^ (δ ^ (5 * ν))
  have hDδ : (D : ℝ) * δ = τstar := hτD.symm
  have h1 : (D : ℝ) * δ ^ (1 + 10 * ν) ≤ δ ^ (5 * ν) / 2 := by
    have e : (D : ℝ) * δ ^ (1 + 10 * ν) = (D * δ) * δ ^ (10 * ν) := by
      rw [Real.rpow_add hδ0, Real.rpow_one]; ring
    rw [e, hDδ]
    have e2 : δ ^ (10 * ν) = δ ^ (5 * ν) * δ ^ (5 * ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    rw [e2]
    calc τstar * (δ ^ (5 * ν) * δ ^ (5 * ν)) = (τstar * δ ^ (5 * ν)) * δ ^ (5 * ν) := by ring
      _ ≤ (1 / 2) * δ ^ (5 * ν) := by gcongr
      _ = _ := by ring
  have hΛ0 : 0 ≤ Real.log L := by linarith
  have h2 : Real.exp ((D : ℝ) * δ ^ (1 + 10 * ν) * Real.log L) ≤ L ^ (δ ^ (5 * ν) / 2) := by
    rw [Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    calc (D : ℝ) * δ ^ (1 + 10 * ν) * Real.log L ≤ (δ ^ (5 * ν) / 2) * Real.log L := by gcongr
      _ = Real.log L * (δ ^ (5 * ν) / 2) := by ring
  calc Real.exp ((D : ℝ) * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4)
      ≤ L ^ (δ ^ (5 * ν) / 2) * L ^ (δ ^ (5 * ν) / 2) := by
        exact mul_le_mul h2 hlog (by positivity) (by positivity)
    _ = L ^ (δ ^ (5 * ν)) := by rw [← Real.rpow_add hLpos]; ring_nf

end WaveTurbulence.Ladder
