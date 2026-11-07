/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS00Sum

/-! # W6, vector-variable version: the superposition theorem (multi-time `K̃^U`) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier MeasureTheory
open scoped ENNReal

variable {r : ℕ} {V : Type*}

/-- Normalise a function of finite sup-norm: `c = w · a`, `w = sup |c|`, `|a| ≤ 1`. -/
theorem exists_normalised00 (c : V → ℂ) (h : (⨆ v, ‖c v‖ₑ) ≠ ⊤) :
    ∃ (w : ℝ) (a : V → ℂ), 0 ≤ w ∧ ENNReal.ofReal w = ⨆ v, ‖c v‖ₑ ∧ (∀ v, ‖a v‖ ≤ 1) ∧
      ∀ v, c v = w * a v := by
  set S := ⨆ v, ‖c v‖ₑ with hS
  set w : ℝ := S.toReal with hw
  have hwe : ENNReal.ofReal w = S := ENNReal.ofReal_toReal h
  have hle : ∀ v, ‖c v‖ ≤ w := fun v => by
    have : ENNReal.ofReal ‖c v‖ ≤ ENNReal.ofReal w := by
      rw [hwe, ofReal_norm]; exact le_iSup (fun v => ‖c v‖ₑ) v
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 this
  by_cases hw0 : w = 0
  · have hc : ∀ v, c v = 0 := fun v => norm_le_zero_iff.1 (by simpa [hw0] using hle v)
    exact ⟨w, 0, ENNReal.toReal_nonneg, hwe, fun v => by simp, fun v => by simp [hc v, hw0]⟩
  · have hwpos : 0 < w := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hw0)
    refine ⟨w, fun v => ((w⁻¹ : ℝ) : ℂ) * c v, ENNReal.toReal_nonneg, hwe, fun v => ?_, fun v => ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_le_one₀ hwpos]
      exact hle v
    · have : (w : ℂ) ≠ 0 := by exact_mod_cast hw0
      push_cast
      field_simp

/-- **W6, vector variables (`𝔛^{θ,0,0}`), arbitrary number of times.**  For `F(t, v)` with
`‖F‖_{𝔛^{θ,0,0}(B × K)} < b`, `B` in a unit time cell, `F = ∑_m w_m a_m(v) e^{πi m·t}` on `B × K`, with
`|a_m| ≤ 1` and `∑_m ⟨m/2⟩^θ w_m ≤ C b`, `C` depending on `(r, θ)` only.  (For `K̃^U`: `r = 3`.) -/
theorem fourier_superposition00 {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
      (f : (Fin r → ℝ) → V → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ v ∈ K, Continuous fun t => f t v) →
      XNorm00Restr θ B K f < b →
      ∃ (w : (Fin r → ℤ) → ℝ) (a : (Fin r → ℤ) → V → ℂ),
        (∀ m, 0 ≤ w m) ∧ (∀ m v, ‖a m v‖ ≤ 1) ∧
        (∀ t ∈ B, ∀ v ∈ K, HasSum (fun m => (w m : ℂ) * a m v * fsPhase m t) (f t v)) ∧
        Summable w ∧
        ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * b := by
  obtain ⟨C0, hC0, hC⟩ := tsum_iSup_coeff00_le (r := r) (V := V) hθ
  refine ⟨ENNReal.ofReal C0, ENNReal.ofReal_ne_top, fun q B K f b hb hBc hBi hfc hn => ?_⟩
  unfold XNorm00Restr at hn
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hn
  obtain ⟨hGK, hGb⟩ := iInf_lt_iff.1 hG
  have hGtop : XNorm00 θ G < ⊤ := lt_of_lt_of_le hGb le_top
  set c : (Fin r → ℤ) → V → ℂ := coeff00 q G with hcdef
  have hbound := hC q G hGtop
  have hfin : ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hGtop.ne))
      (hbound)
  have hc : ∀ m, (⨆ v, ‖c m v‖ₑ) ≠ ⊤ := by
    intro m htop
    have h1 : maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hfin
        (ENNReal.le_tsum (f := fun m => maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ) m)
    apply h1
    rw [htop, ENNReal.mul_top]
    exact (lt_of_lt_of_le one_pos (one_le_maxBracketPow hθ (half m))).ne'
  choose w a hw0 hwe ha hca using fun m => exists_normalised00 (c m) (hc m)
  have hsum_eq : ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) =
      ∑' m, maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ :=
    tsum_congr fun m => by rw [hwe m]
  refine ⟨w, a, hw0, ha, fun t ht v hv => ?_, ?_, ?_⟩
  · refine (hasSum_coeff00 hθ q hBc (fun t' ht' => hGK t' ht' v hv) (hfc v hv) hGtop
      (hBi ht)).congr_fun ?_
    intro m
    show _ = c m v * fsPhase m t
    rw [hca m v]
  · refine summable_of_tsum_ofReal_ne_top hw0 ?_
    refine ne_top_of_le_ne_top hfin ?_
    rw [← hsum_eq]
    exact ENNReal.tsum_le_tsum fun m => le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ _)
  · rw [hsum_eq]
    exact hbound.trans (mul_le_mul_right hGb.le _)

end WaveTurbulence.RepAnalytic
