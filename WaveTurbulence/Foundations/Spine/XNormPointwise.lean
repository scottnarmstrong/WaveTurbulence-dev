/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimePointwise
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Pointwise control from the exact snapshot mixed norm, with temporal continuity proved separately. -/
public section
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set
open scoped ENNReal

theorem XNorm00_le_XNorm {r d : ℕ} (θ : ℝ) (A B : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) : XNorm00 θ F ≤ XNorm θ A B F := by
  classical
  unfold XNorm00 XNorm
  by_cases hG : (∀ k, Integrable fun t => F t k) ∧ (A = 0 ∨ ∀ᵐ lam, ContDiff ℝ A (timeFT F lam))
  · rw [ite_eq_left hG.1, ite_eq_left hG]
    have hz : (∑ _ : Fin d, (0 : ℕ)) ≤ A := by simp
    refine le_trans ?_ (le_iSup_of_le (fun _ : Fin d => (0 : ℕ)) (le_iSup_of_le hz le_rfl))
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    apply iSup_le
    intro k
    apply le_iSup_of_le k
    rw [Induct.iterPartial_zero_index, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (Induct.one_le_jbr k))
  · rw [ite_eq_right hG]
    exact le_top

theorem XNorm00Restr_le_XNormRestr {r d : ℕ} (θ : ℝ) (A B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm00Restr θ T K F ≤ XNormRestr θ A B T K F := by
  unfold XNorm00Restr XNormRestr
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  have h0 : (⨅ (H : (Fin r → ℝ) → Mom d → ℂ)
      (_ : ∀ t ∈ T, ∀ k ∈ K, H t k = F t k), XNorm00 θ H) ≤ XNorm00 θ G :=
    iInf_le_of_le G (iInf_le_of_le hG le_rfl)
  exact h0.trans (XNorm00_le_XNorm θ A B G)

/-- No mixed-guard measurability premise is needed: choose the zero multi-index directly. -/
theorem enorm_le_XNormRestr_of_continuous {r d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (A B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ)
    (t : Fin r → ℝ) (k : Mom d) (ht : t ∈ closure (interior T)) (hk : k ∈ K)
    (hc : Continuous (fun s => F s k)) : ‖F t k‖ₑ ≤ XNormRestr θ A B T K F := by
  apply (enorm_le_mixedRestrictionNorm00_closure_interior hθ T K F t k ht hk hc).trans
  rw [← NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
  exact XNorm00Restr_le_XNormRestr θ A B T K F

end WaveTurbulence.LGSpine
