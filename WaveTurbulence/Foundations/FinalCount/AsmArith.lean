/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! **FINALCOUNT-ASSEMBLY, E: the real-exponent bookkeeping of TARGET (together2), (together3), L2201-L2229.**

Pure real arithmetic (no molecules).  Notation: `γ₀ = min γ (1-γ)`, `a = 2γ₀+5η²`, `b = γ₀+2η²`.

* `alpha_label_cancel`: the `α`-label factors of an operation (`excessRHS`) and of the final bound (`finalcount`) cancel.
* `exponent_bookkeeping`: `Σ ΔF = F_fin - 1`, `Σ ΔV_β = V_β`, and the perfect-component `G`-terms leave `a (F_im - 1)` (together2).
* `final_exponent_le`: (together3), with the operation-count slack `η³/4` per operation (spent on the number of
  classes and on the per-operation constants), `p_sb ≤ 2 p_op` (erratum at TARGET L2216), `ρ_fin ≥ ρ_sb - C₀ p_op`.
* `d_gamma_slack`: `4γ₀ ≤ d - γ - 1/2` for `3 ≤ d`, `0 < γ < 1`.
* `polylog_absorb`: `K (1 + log L)^c ≤ L^ε` for large `L`.
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountAsm

/-- `4γ₀ ≤ d - γ - 1/2` (the closing remark of TARGET L2229, `d - γ - 4γ₀ ≥ 1/2`), for `3 ≤ d`, `0 < γ < 1`. -/
theorem d_gamma_slack (d γ : ℝ) (hd : 3 ≤ d) (_hγ0 : 0 < γ) (_hγ1 : γ < 1) :
    4 * min γ (1 - γ) ≤ d - γ - 1 / 2 := by
  rcases le_total γ (1 - γ) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- Polylogarithmic absorption: `K (1 + log L)^c ≤ L^ε` for all large `L`. -/
theorem polylog_absorb (K : ℝ) (c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, K * (1 + Real.log L) ^ c ≤ L ^ ε := by
  have h1 : (fun L : ℝ => (1 + Real.log L) ^ c) =o[Filter.atTop] fun L => L ^ ε := by
    have h2 : (fun L : ℝ => (Real.log L) ^ c) =o[Filter.atTop] fun L => L ^ ε :=
      by simpa [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (c : ℝ) hε
    have h3 : (fun L : ℝ => (1 + Real.log L) ^ c) =O[Filter.atTop] fun L => (Real.log L) ^ c := by
      refine Asymptotics.IsBigO.of_bound (2 ^ c) ?_
      filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with L hL
      have hlog : 1 ≤ Real.log L := by
        rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hL)]; exact hL
      have h0 : 0 ≤ Real.log L := by linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) c),
        abs_of_nonneg (pow_nonneg h0 c), ← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) c
    exact h3.trans_isLittleO h2
  have h4 := (h1.const_mul_left K).bound (c := 1) one_pos
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 h4
  refine ⟨max L₁ 1, le_max_right _ _, fun L hL => ?_⟩
  have := hL₁ L (le_trans (le_max_left _ _) hL)
  have hL0 : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hL)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_pos (Real.rpow_pos_of_pos hL0 ε)] at this
  exact (le_abs_self _).trans this

end WaveTurbulence.FinalCountAsm
