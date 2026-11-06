/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.MultiExpand
public import WaveTurbulence.Foundations.Spine.XNormPointwise

/-!
# Weighted pointwise control from the snapshot norms

The zeroth multi-index of the snapshot norm `XNorm θ A B` (TARGET (normX), L581) carries the momentum
weight `⟨k⟩^B`. Hence (`enorm_weight_le_XNormRestr_of_continuous`), for a function continuous in time and
a time point in the closure of the interior of the box,
`⟨k⟩^B |F(t, k)| ≤ ‖F‖_{𝔛^{θ,A,B}(T)}`. Only the zeroth multi-index is used, so no measurability of the
higher-order integrands is needed (the spine's `enorm_le_XNormRestr_of_continuous`, with the weight).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.PL234

open WaveTurbulence.LGSpine

variable {r d : ℕ}

theorem XNorm00_weight_le_XNorm (θ : ℝ) (A B : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm00 θ (fun t k => ((jbr k ^ B : ℝ) : ℂ) * F t k) ≤ XNorm θ A B F := by
  classical
  by_cases hi : ∀ k, Integrable fun t => F t k
  · by_cases hg : (∀ k, Integrable fun t => F t k) ∧ (A = 0 ∨ ∀ᵐ lam, ContDiff ℝ A (timeFT F lam))
    · unfold XNorm00 XNorm
      rw [ite_eq_left fun k => (hi k).const_mul _, ite_eq_left hg]
      have hz : (∑ _ : Fin d, (0 : ℕ)) ≤ A := by simp
      refine le_trans (b := ∫⁻ ξ : Fin r → ℝ, maxBracketPow θ ξ *
        ⨆ k, ENNReal.ofReal (jbr k ^ B * ‖iterPartial (fun _ => 0) (timeFT F ξ) k‖)) ?_
        (le_iSup_of_le (fun _ : Fin d => (0 : ℕ)) (le_iSup_of_le hz le_rfl))
      apply lintegral_mono
      intro ξ
      apply mul_le_mul_right
      apply iSup_le
      intro k
      apply le_iSup_of_le k
      have hft : timeFT (fun t k => ((jbr k ^ B : ℝ) : ℂ) * F t k) ξ k =
          ((jbr k ^ B : ℝ) : ℂ) * timeFT F ξ k := by
        unfold timeFT
        rw [← integral_const_mul]
        congr 1
        funext t
        ring
      rw [hft, WaveTurbulence.Induct.iterPartial_zero_index, ← ofReal_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (pow_nonneg (le_trans zero_le_one (WaveTurbulence.Induct.one_le_jbr k)) _)]
    · unfold XNorm
      rw [ite_eq_right hg]
      exact le_top
  · unfold XNorm
    rw [ite_eq_right (fun h => hi h.1)]
    exact le_top

theorem XNorm00Restr_weight_le_XNormRestr (θ : ℝ) (A B : ℕ) (T : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm00Restr θ T K (fun t k => ((jbr k ^ B : ℝ) : ℂ) * F t k) ≤ XNormRestr θ A B T K F := by
  unfold XNorm00Restr XNormRestr
  refine le_iInf fun G => le_iInf fun hG => ?_
  have h0 : (⨅ (H : (Fin r → ℝ) → Mom d → ℂ)
      (_ : ∀ t ∈ T, ∀ k ∈ K, H t k = ((jbr k ^ B : ℝ) : ℂ) * F t k), XNorm00 θ H) ≤
      XNorm00 θ (fun t k => ((jbr k ^ B : ℝ) : ℂ) * G t k) :=
    iInf_le_of_le (fun t k => ((jbr k ^ B : ℝ) : ℂ) * G t k)
      (iInf_le_of_le (fun t ht k hk => by
        show ((jbr k ^ B : ℝ) : ℂ) * G t k = _
        rw [hG t ht k hk]) le_rfl)
  exact h0.trans (XNorm00_weight_le_XNorm θ A B G)

/-- **Weighted pointwise control from the restriction norm.** -/
theorem enorm_weight_le_XNormRestr_of_continuous {θ : ℝ} (hθ : 0 ≤ θ) (A B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ)
    (t : Fin r → ℝ) (k : Mom d) (ht : t ∈ closure (interior T)) (hk : k ∈ K)
    (hc : Continuous (fun s => F s k)) :
    ENNReal.ofReal (jbr k ^ B * ‖F t k‖) ≤ XNormRestr θ A B T K F := by
  have hc' : Continuous (fun s => ((jbr k ^ B : ℝ) : ℂ) * F s k) := continuous_const.mul hc
  have e : ENNReal.ofReal (jbr k ^ B * ‖F t k‖) = ‖((jbr k ^ B : ℝ) : ℂ) * F t k‖ₑ := by
    rw [← ofReal_norm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (le_trans zero_le_one (WaveTurbulence.Induct.one_le_jbr k)) _)]
  rw [e]
  apply (enorm_le_mixedRestrictionNorm00_closure_interior hθ T K
    (fun ts k => ((jbr k ^ B : ℝ) : ℂ) * F ts k) t k ht hk hc').trans
  have hb := NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (V := Mom d) θ T K
    (fun ts k => ((jbr k ^ B : ℝ) : ℂ) * F ts k)
  exact hb.symm.le.trans (XNorm00Restr_weight_le_XNormRestr θ A B T K F)

end WaveTurbulence.PL234
