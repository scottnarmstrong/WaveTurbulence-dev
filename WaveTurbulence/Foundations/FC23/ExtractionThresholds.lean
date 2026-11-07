/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.ExtractionNumerics
public import WaveTurbulence.Foundations.FC23.StageOrderGrowth
/-! Explicit early-delta and late-L choices for every permitted total order. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Filter

def extractionDelta (w : ℕ) (ν : ℝ) : ℝ :=
  Real.exp (-(Real.log (4 * Real.exp 1) * (2 * w : ℕ)) / (6 * ν))

theorem extractionDelta_pos (w : ℕ) (ν : ℝ) : 0 < extractionDelta w ν := Real.exp_pos _

theorem extractionDelta_bound {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) (w : ℕ)
    (hsmall : δ ≤ extractionDelta w ν) :
    (4 * Real.exp 1) ^ (2 * w) * δ ^ (6 * ν) ≤ 1 := by
  have hpow := Real.rpow_le_rpow hδ.le hsmall (by positivity : 0 ≤ 6 * ν)
  apply (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (4 * Real.exp 1) ^ (2 * w))).trans_eq
  unfold extractionDelta
  rw [← Real.exp_mul]
  have he : (-(Real.log (4 * Real.exp 1) * ((2 * w : ℕ) : ℝ)) / (6 * ν)) * (6 * ν) =
      -(Real.log (4 * Real.exp 1) * ((2 * w : ℕ) : ℝ)) := by field_simp
  rw [he, show (4 * Real.exp 1) ^ (2 * w) =
      Real.exp (Real.log (4 * Real.exp 1) * ((2 * w : ℕ) : ℝ)) from by
    rw [mul_comm (Real.log _) _, Real.exp_nat_mul, Real.exp_log (by positivity)], ← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem eventually_extraction_controls (S X : ℕ) (hS : 0 < S) {C U : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ ∀ N : ℕ, (N : ℝ) ≤ Real.log L ^ X →
      4 * ((2 * N + 1 : ℕ) : ℝ) ≤ L ∧
      C * ((2 * N + 1 : ℕ) : ℝ) * U * (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ S ≤ L ^ S ∧
      3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) ≤ L := by
  have h1 := eventually_degree_cost (C := 4) (b := 1) (by norm_num) (by norm_num) 1 X
  have h2 := eventually_degree_cost (C := 4 ^ S * C * U) (b := (S : ℝ))
    (by positivity) (by exact_mod_cast hS) (S + 1) X
  have h3 := eventually_degree_cost (C := 3 * (4 * Real.exp 1) * 4 ^ S * C * U) (b := 1)
    (by positivity) (by norm_num) (S + 2) X
  filter_upwards [h1, h2, h3, eventually_ge_atTop (2 : ℝ)] with L h1 h2 h3 hL
  refine ⟨hL, fun N hN => ⟨?_, ?_, ?_⟩⟩
  · simpa only [pow_one, Real.rpow_one] using h1 N hN
  · have hh := h2 N hN
    rw [Real.rpow_natCast] at hh
    convert hh using 1
    rw [mul_pow, pow_succ]
    ring
  · simpa only [Real.rpow_one] using h3 N hN

theorem extraction_scale_controls (S N : ℕ) {C U L M : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hL : 0 < L) (hLM : L ≤ M)
    (hA : 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ L)
    (hρ : C * ((2 * N + 1 : ℕ) : ℝ) * U * (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ S ≤ L ^ S) :
    1 ≤ M / (4 * ((2 * N + 1 : ℕ) : ℝ)) ∧ 1 ≤ extractionRadius S N C U M := by
  have hD : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  refine ⟨(one_le_div (by positivity)).mpr (hA.trans hLM), ?_⟩
  unfold extractionRadius
  apply (one_le_div (by positivity)).mpr
  rw [div_pow]
  apply (le_div_iff₀ (by positivity)).mpr
  exact hρ.trans (pow_le_pow_left₀ hL.le hLM S)
end WaveTurbulence.FC23
