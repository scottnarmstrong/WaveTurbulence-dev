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

/-- Pairing of an `α`-atom's operation factor `L^e Q` with its final-bound factor `L^{-e} Q⁻¹`. -/
theorem alpha_label_cancel (L e Q : ℝ) (hL : 0 < L) (hQ : 0 < Q) :
    (L ^ e * Q) * (L ^ (-e) * Q⁻¹) = 1 := by
  rw [Real.rpow_neg hL.le]
  field_simp

/-- Product version, over any finite index set of `α`-atoms with labels `(Q i, κ i)`. -/
theorem alpha_label_prod_cancel {ι : Type*} (s : Finset ι) (L g η : ℝ) (Q : ι → ℝ) (κ : ι → ℝ)
    (hL : 0 < L) (hQ : ∀ i, 0 < Q i) :
    (∏ i ∈ s, (L ^ ((g + 3 * η) / 2 - κ i * η) * Q i)) *
      (∏ i ∈ s, (L ^ (-((g + 3 * η) / 2) + κ i * η) * (Q i)⁻¹)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have := alpha_label_cancel L ((g + 3 * η) / 2 - κ i * η) (Q i) hL (hQ i)
  rwa [show -((g + 3 * η) / 2 - κ i * η) = -((g + 3 * η) / 2) + κ i * η by ring] at this

/-- (together2), the `F`/`V_β`/`G` part: with `F_fin = F_im + F_perf` (components are perfect or imperfect),
`Σ ΔF = F_fin - F_sb`, `F_sb = 1`, `Σ ΔV_β = V_β`, `Σ_comp G = F_perf`, `Σ_comp V_β(comp) = V_β`. -/
theorem exponent_bookkeeping (a b Ffin Fim Fperf Vb : ℝ) (h : Ffin = Fim + Fperf) :
    a * (Ffin - 1) - b * Vb + (b * Vb - a * Fperf) = a * (Fim - 1) := by
  subst h; ring

/-- `4γ₀ ≤ d - γ - 1/2` (the closing remark of TARGET L2229, `d - γ - 4γ₀ ≥ 1/2`), for `3 ≤ d`, `0 < γ < 1`. -/
theorem d_gamma_slack (d γ : ℝ) (hd : 3 ≤ d) (_hγ0 : 0 < γ) (_hγ1 : γ < 1) :
    4 * min γ (1 - γ) ≤ d - γ - 1 / 2 := by
  rcases le_total γ (1 - γ) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- **(together3), exponent form.**  The exponent of (together2) with the slack `3/4 η³ p_op` per operation (the
remaining `η³/4` per operation pays for the number of run types and the per-operation constants), bounded by the exponent
of `finalcount1`.  `γ₀ = min γ (1-γ)`; `p_sb ≤ 2 p_op` is the corrected TARGET L2216 (`p_sb ≤ p_op` there). -/
theorem final_exponent_le (d γ η R ρsb ρfin psb pop pplus Fim Z C₀ : ℝ)
    (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hC₀ : C₀ * η ^ 2 ≤ 1 / 4)
    (hR : 1 ≤ R) (hFim : Fim ≤ R) (hpplus : pplus ≤ 2 * R - 2) (hZ : Z ≤ 4 * (R - 1))
    (hρsb : 0 ≤ ρsb) (_hpsb : 0 ≤ psb) (hpop : 0 ≤ pop) (hpsb2 : psb ≤ 2 * pop) (hρ : ρsb - C₀ * pop ≤ ρfin) :
    (2 * min γ (1 - γ) + 5 * η ^ 2) * (Fim - 1) + min γ (1 - γ) * pplus + η * Z
        - η ^ 5 * ρfin - (3 / 4) * η ^ 3 * pop ≤
      -4 * η ^ 6 * (ρsb + psb) + (R - 1) * (d - γ - 1 / 4 - 1 / 40) := by
  have hγ0' : 0 ≤ min γ (1 - γ) := le_min hγ0.le (by linarith)
  have hslack := d_gamma_slack d γ hd hγ0 hγ1
  have hη2 : 0 < η ^ 2 := by positivity
  have hη3 : 0 < η ^ 3 := by positivity
  have hη5 : 0 < η ^ 5 := by positivity
  have hη6 : 0 < η ^ 6 := by positivity
  have h6 : 4 * η ^ 6 ≤ η ^ 5 := by nlinarith [mul_pos hη5 hη0]
  have hη3' : η ^ 3 ≤ 1 / 16 := by
    have : η ^ 3 ≤ (1 / 20) ^ 3 := pow_le_pow_left₀ hη0.le hη 3
    nlinarith
  have hC5 : C₀ * η ^ 5 * pop ≤ (1 / 4) * η ^ 3 * pop := by
    have : C₀ * η ^ 5 = (C₀ * η ^ 2) * η ^ 3 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hC₀ hη3.le
    exact mul_le_mul_of_nonneg_right (by linarith) hpop
  have hpsb' : 8 * η ^ 6 * pop ≥ 4 * η ^ 6 * psb := by nlinarith
  have hpsb'' : 8 * η ^ 6 * pop ≤ (1 / 2) * η ^ 3 * pop := by
    have : 8 * η ^ 6 = (8 * η ^ 3) * η ^ 3 := by ring
    rw [this]; nlinarith [mul_nonneg hη3.le hpop]
  have hρ5 : η ^ 5 * ρfin ≥ η ^ 5 * ρsb - C₀ * η ^ 5 * pop := by nlinarith
  have hρ6 : η ^ 5 * ρsb ≥ 4 * η ^ 6 * ρsb := by nlinarith
  have hR1 : 0 ≤ R - 1 := by linarith
  have hS : 4 * η + 5 * η ^ 2 ≤ 9 / 40 := by nlinarith
  have hA : (2 * min γ (1 - γ) + 5 * η ^ 2) * (Fim - 1) ≤ (2 * min γ (1 - γ) + 5 * η ^ 2) * (R - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hB : min γ (1 - γ) * pplus ≤ min γ (1 - γ) * (2 * (R - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ0'
  have hZ' : η * Z ≤ η * (4 * (R - 1)) := mul_le_mul_of_nonneg_left hZ hη0.le
  have hT : (4 * min γ (1 - γ) + 4 * η + 5 * η ^ 2) * (R - 1) ≤ (d - γ - 1 / 4 - 1 / 40) * (R - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hR1
  nlinarith

/-- Monotonicity of `L ↦ L^x`, `1 ≤ L`. -/
theorem rpow_le_rpow_of_le_exp {L x y : ℝ} (hL : 1 ≤ L) (h : x ≤ y) : L ^ x ≤ L ^ y :=
  Real.rpow_le_rpow_of_exponent_le hL h

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
