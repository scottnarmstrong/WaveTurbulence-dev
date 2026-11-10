/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev5
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev6
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the slack lemma of a cluster erasure** (set version of `erase_table`).

For `d ≥ 3`, `γ ∈ (0,1)`, `η ≤ γ₀/1000`, `C₀ η⁴ ≤ 1`, `L` large, `C₁ ≥ 1`, `0 < δ ≤ 1`, a cluster with `m = |K| ≥ 1` atoms, `e ≤ 4m` bonds
to the outside and rank drop `j`:
`N · rankFactor(j) · (log L)^{c₀ (m+e)} ≤ L^{-η³ + a(m - j) - η e - C₀ η⁵ (m + e)}`, `a = 2γ₀ + 5η²`, with
`N = 1` if `0 ≤ j` (pinned) and `N = (⌊2L⌋+1)^d` if `m + 1 ≤ j` (unpinned: `j ≥ |K| + 1`, R29 item 4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

theorem polylog_pow_le {E : ℝ} (hE : 0 < E) (n : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → Real.log L ^ n ≤ L ^ E := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, le_rfl, fun L hL => by simpa using Real.one_le_rpow hL hE.le⟩
  set ε := E / (2 * n) with hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 < ε := by positivity
  set M := 1 / ε ^ n + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have : 0 ≤ 1 / ε ^ n := by positivity
                         linarith
  refine ⟨max 1 (M ^ (2 / E)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hlog : Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hL0.le hε0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have h6 : Real.log L ^ n ≤ (L ^ ε / ε) ^ n := pow_le_pow_left₀ hlog0 hlog n
  have e6 : (L ^ ε / ε) ^ n = L ^ (E / 2) / ε ^ n := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 2
    rw [hε]; field_simp
  have hLE : M ≤ L ^ (E / 2) := by
    have h1 : M ^ (2 / E) ≤ L := (le_max_right _ _).trans hL
    have h2 : (M ^ (2 / E)) ^ (E / 2) ≤ L ^ (E / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 (by positivity)
    rwa [← Real.rpow_mul (by linarith), show 2 / E * (E / 2) = 1 by field_simp, Real.rpow_one] at h2
  have hsplit : L ^ E = L ^ (E / 2) * L ^ (E / 2) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  calc Real.log L ^ n ≤ L ^ (E / 2) / ε ^ n := by rw [← e6]; exact h6
    _ = (1 / ε ^ n) * L ^ (E / 2) := by ring
    _ ≤ M * L ^ (E / 2) := by
        have : 1 / ε ^ n ≤ M := by rw [hM]; linarith
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hL0.le _)
    _ ≤ L ^ (E / 2) * L ^ (E / 2) := mul_le_mul_of_nonneg_right hLE (Real.rpow_nonneg hL0.le _)
    _ = L ^ E := hsplit.symm

end WaveTurbulence.FinalCountG3
