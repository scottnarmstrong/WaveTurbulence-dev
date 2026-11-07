/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.XChain.JbrBounds
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # `XNorm00 ≤ XNorm` for the snapshot-9 norm (split off `Pointwise` so that `FSMain` is light). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory Set
open scoped ENNReal

/-- `‖F‖_{𝔛^{θ,0,0}} ≤ ‖F‖_{𝔛^{θ,Λ₁,Λ₂}}` for the snapshot-9 norm. -/
theorem XNorm00_le_XNorm {r d : ℕ} (θ : ℝ) (A B : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) : XNorm00 θ F ≤ XNorm θ A B F := by
  classical
  unfold XNorm00 XNorm
  by_cases h2 : (∀ k, Integrable fun t => F t k) ∧ (A = 0 ∨ ∀ᵐ lam, ContDiff ℝ A (timeFT F lam))
  · rw [if_pos h2, if_pos h2.1]
    have hz : (∑ _ : Fin d, (0 : ℕ)) ≤ A := by simp
    refine le_trans (b := ∫⁻ ξ : Fin r → ℝ, maxBracketPow θ ξ *
      ⨆ k, ENNReal.ofReal (jbr k ^ B * ‖iterPartial (fun _ => 0) (timeFT F ξ) k‖)) ?_
      (le_iSup_of_le (fun _ : Fin d => (0 : ℕ)) (le_iSup_of_le hz le_rfl))
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    apply iSup_mono
    intro k
    rw [Induct.iterPartial_zero_index, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (Induct.one_le_jbr k))
  · rw [if_neg h2]; exact le_top

end WaveTurbulence.VineEstS3
