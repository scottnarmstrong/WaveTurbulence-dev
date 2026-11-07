/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSNorm
public import WaveTurbulence.Foundations.VineEst.VineEstS3.XNormLe

/-! # Fourier-series expansion of a restriction-norm bounded kernel on a unit cell (B2, step 7)

If `f(t,k)` is continuous in `t ∈ ℝ^r` for every `k ∈ K`, and `‖f‖_{𝔛^{θ,Λ₁,Λ₂}(B × K)} < b` (`B ⊆ Q_q`,
`B ⊆ closure (interior B)`), then there are momentum functions `c_m` with
`f(t,k) = ∑_m c_m(k) e^{πi m·t}` for `t ∈ B`, `k ∈ K`, and
`∑_m ⟨m/2⟩^θ ‖c_m‖_{S^{Λ₁,Λ₂}} ≤ C · b`, with `C` independent of `f`, `b`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

variable {r d : ℕ}

/-- **Fourier-series expansion on a unit cell.** -/
theorem fs_expansion {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (f : (Fin r → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k ∈ K, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B K f < b →
      ∃ c : (Fin r → ℤ) → Mom d → ℂ,
        (∀ t ∈ B, ∀ k ∈ K, HasSum (fun m : Fin r → ℤ => c m k * fsPhase m t) (f t k)) ∧
        ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b := by
  obtain ⟨C, hC, hCb⟩ := sum_SNorm_coeff_le (r := r) (d := d) hθ hΛ
  refine ⟨C, hC, fun q B K f b hBc hBi hfc hb => ?_⟩
  unfold XNormRestr at hb
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hb
  obtain ⟨hGK, hGb⟩ := iInf_lt_iff.1 hG
  have hGtop : XNorm θ Λ₁ Λ₂ G < ⊤ := lt_of_lt_of_le hGb le_top
  refine ⟨coeff q G, fun t htB k hk => ?_, ?_⟩
  · exact hasSum_coeff_at hθ q hBc (fun t' ht' => hGK t' ht' k hk) (hfc k hk)
      ((XNorm00_le_XNorm θ Λ₁ Λ₂ G).trans_lt hGtop) (hBi htB)
  · exact (hCb q G hGtop).trans (mul_le_mul_right hGb.le _)

end WaveTurbulence.VineEstS3.FS
