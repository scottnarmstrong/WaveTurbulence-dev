/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! # Monotonicity of the landed spatial norms in their two orders -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp

/-- Lowering the polynomial momentum weight decreases the weighted supremum. -/
theorem momentumSupNorm_mono {d W M : ℕ} (hWM : W ≤ M) (f : Mom d → ℂ) :
    Fourier.momentumSupNorm W f ≤ Fourier.momentumSupNorm M f := by
  unfold Fourier.momentumSupNorm
  apply iSup_le
  intro k
  apply le_iSup_of_le k
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (pow_le_pow_right₀ (Incoh.one_le_momentumBracket k) hWM)) le_rfl

/-- Lowering either the derivative order or the polynomial weight
preserves the full landed spatial norm bound, including its smoothness guard. -/
theorem spatialNorm_mono {d N W K M : ℕ} (hNK : N ≤ K) (hWM : W ≤ M) (f : Mom d → ℂ) :
    Fourier.spatialNorm N W f ≤ Fourier.spatialNorm K M f := by
  classical
  by_cases hc : K=0 ∨ ContDiff ℝ K f
  · have hn : N=0 ∨ ContDiff ℝ N f := by
      rcases hc with hk | hf
      · left
        omega
      · exact Or.inr (hf.of_le (by exact_mod_cast hNK))
    rw [Fourier.spatialNorm,ite_eq_left hn,Fourier.spatialNorm,ite_eq_left hc]
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply iSup_le
    intro ρ
    exact le_iSup_of_le j (le_iSup_of_le (hj.trans hNK)
      (le_iSup_of_le ρ (momentumSupNorm_mono hWM _)))
  · have he : Fourier.spatialNorm K M f = ⊤ := by
      rw [Fourier.spatialNorm,ite_eq_right hc]
    rw [he]
    exact le_top

end WaveTurbulence.RegAsymp
