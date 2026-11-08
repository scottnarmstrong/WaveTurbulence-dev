/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FlCoef.Class

/-!
# FL-COEF: the moment bound and the tail bound (8.4)

Supplement Lemma 8.1, second estimate of (8.3) and estimate (8.4). The moment weight is an
arbitrary extended-real weight `ω(α)` (in the supplement `max_j ⟨α_j⟩^{1-η/2}`), and the `λ`-weight
`W(γ)` an arbitrary function of the auxiliary variables.

* `lintegral_mulSym_le`: a multiplier of absolute value at most one does not increase the weighted
  `L¹` norm (cutoffs are at most one).
* `lintegral_mulSym_tail_le`: if in addition the multiplier vanishes unless `|α_j| ≥ S/2`, the
  weighted norm *without* the `α`-weight is at most `(S/2)^{-p}` times the moment bound.
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.Flower.FlCoef

open WaveTurbulence.ClassJR MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] {Γ : Type*} [MeasureSpace Γ]

/-- **Second estimate of (8.3).** `‖F‖ ≤ 1` does not increase any weighted `L¹` norm. -/
theorem lintegral_mulSym_le {F : (ι → ℝ) → ℂ} (hF : ∀ α, ‖F α‖ₑ ≤ 1) (m : (ι → ℝ) → Γ → ℂ)
    (W : (ι → ℝ) → Γ → ℝ≥0∞) :
    ∫⁻ α, ∫⁻ γ, W α γ * ‖mulSym F m α γ‖ₑ ≤ ∫⁻ α, ∫⁻ γ, W α γ * ‖m α γ‖ₑ := by
  refine lintegral_mono fun α => lintegral_mono fun γ => ?_
  unfold mulSym
  rw [enorm_mul]
  gcongr
  calc ‖F α‖ₑ * ‖m α γ‖ₑ ≤ 1 * ‖m α γ‖ₑ := by gcongr; exact hF α
    _ = _ := one_mul _

/-- **Estimate (8.4).** Let `F` be bounded by one and vanish unless `|α_j| ≥ S/2` (`S > 0`, `p ≥ 0`),
and let `ω` be a weight with `⟨α_j⟩^p ≤ ω(α)`, where `⟨x⟩ = √(1+x²)`. Then
`∫∫ W ‖F m‖ ≤ (S/2)^{-p} ∫∫ W ω ‖m‖`. -/
theorem lintegral_mulSym_tail_le {F : (ι → ℝ) → ℂ} (hF : ∀ α, ‖F α‖ₑ ≤ 1) (j : ι) {S p : ℝ}
    (hS : 0 < S) (hp : 0 ≤ p) (hsupp : ∀ α, F α ≠ 0 → S / 2 ≤ |α j|)
    (m : (ι → ℝ) → Γ → ℂ) (W : (ι → ℝ) → Γ → ℝ≥0∞) (ω : (ι → ℝ) → ℝ≥0∞)
    (hω : ∀ α, ENNReal.ofReal (Real.sqrt (1 + α j ^ 2) ^ p) ≤ ω α) :
    ∫⁻ α, ∫⁻ γ, W α γ * ‖mulSym F m α γ‖ₑ ≤
      ENNReal.ofReal ((S / 2) ^ (-p)) * ∫⁻ α, ∫⁻ γ, W α γ * ω α * ‖m α γ‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun α => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun γ => ?_
  by_cases h0 : F α = 0
  · simp [mulSym, h0]
  · have hx := hsupp α h0
    have hS2 : 0 < S / 2 := by positivity
    have h1 : (S / 2) ^ p ≤ Real.sqrt (1 + α j ^ 2) ^ p :=
      Real.rpow_le_rpow hS2.le (hx.trans ((Real.abs_le_sqrt (by nlinarith)))) hp
    have h2 : 1 ≤ (S / 2) ^ (-p) * Real.sqrt (1 + α j ^ 2) ^ p := by
      rw [Real.rpow_neg hS2.le]
      have hp0 : 0 < (S / 2) ^ p := Real.rpow_pos_of_pos hS2 p
      rw [inv_mul_eq_div, le_div_iff₀ hp0, one_mul]
      exact h1
    have h3 : 1 ≤ ENNReal.ofReal ((S / 2) ^ (-p)) * ω α :=
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ ENNReal.ofReal ((S / 2) ^ (-p) * Real.sqrt (1 + α j ^ 2) ^ p) :=
            ENNReal.ofReal_le_ofReal h2
        _ = ENNReal.ofReal ((S / 2) ^ (-p)) * ENNReal.ofReal (Real.sqrt (1 + α j ^ 2) ^ p) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ _ := by gcongr; exact hω α
    have h4 : ‖mulSym F m α γ‖ₑ ≤ ‖m α γ‖ₑ := by
      unfold mulSym
      rw [enorm_mul]
      calc ‖F α‖ₑ * ‖m α γ‖ₑ ≤ 1 * ‖m α γ‖ₑ := by gcongr; exact hF α
        _ = _ := one_mul _
    calc W α γ * ‖mulSym F m α γ‖ₑ ≤ W α γ * ‖m α γ‖ₑ := by gcongr
      _ = W α γ * 1 * ‖m α γ‖ₑ := by rw [mul_one]
      _ ≤ W α γ * (ENNReal.ofReal ((S / 2) ^ (-p)) * ω α) * ‖m α γ‖ₑ := by gcongr
      _ = _ := by ring

/-- The `(4k)!` normalization of the supplement is implied by main's `(2k)!` normalization. -/
theorem gev_le_four_factorial {N A : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) (k : ℕ) :
    gev N A k ≤ ENNReal.ofReal (N * A ^ k * (Nat.factorial (4 * k) : ℝ)) := by
  unfold gev
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact_mod_cast Nat.factorial_le (by omega)

end WaveTurbulence.Flower.FlCoef
