/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Norm00VProduct
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication

/-!
# Smooth cutoff multiplication for arbitrary vector parameters

TARGET L581, L589. The multiplier constant is the same finite scalar
constant as in the landed time Fourier theory, at every real regularity.
-/

public section

namespace WaveTurbulence.Fourier
open MeasureTheory Set
open scoped ENNReal ContDiff

/-- A multiplier independent of the vector parameter costs at most its scalar norm. -/
theorem mixedFourierNorm00_const_param_le {r : ℕ} {V : Type*} (θ : ℝ)
    (f : (Fin r → ℝ) → ℂ) :
    mixedFourierNorm00 θ (fun t (_ : V) => f t) ≤ timeFourierNorm θ f := by
  by_cases hf : Integrable f
  · rw [mixedFourierNorm00_eq_lintegral (fun _ => hf), timeFourierNorm_eq_lintegral hf]
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    exact iSup_le (fun _ => le_rfl)
  · rw [timeFourierNorm_of_not_integrable hf]
    exact le_top

/-- Smooth compactly supported scalar cutoffs multiply the general-variable mixed norm. -/
theorem mixedFourierNorm00_mul_cutoff_le {r : ℕ} {V : Type*} (θ : ℝ)
    {F : (Fin r → ℝ) → V → ℂ} {κ : (Fin r → ℝ) → ℂ}
    (hF : mixedFourierNorm00 θ F < ⊤) (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    mixedFourierNorm00 θ (fun t v => F t v * κ t) ≤
      cutoffMultiplierConstant θ κ * mixedFourierNorm00 θ F := by
  have hk := timeFourierNorm_lt_top_of_smooth_compact |θ| hκ hs
  have hkn : mixedFourierNorm00 |θ| (fun t (_ : V) => κ t) < ⊤ :=
    (mixedFourierNorm00_const_param_le |θ| κ).trans_lt hk
  calc
    _ ≤ ENNReal.ofReal (2 ^ |θ|) * mixedFourierNorm00 θ F *
        mixedFourierNorm00 |θ| (fun t (_ : V) => κ t) :=
      mixedFourierNorm00_mul_asymmetric_le θ (fun _ => hs.continuous) hF hkn
    _ ≤ ENNReal.ofReal (2 ^ |θ|) * mixedFourierNorm00 θ F * timeFourierNorm |θ| κ :=
      mul_le_mul_right (mixedFourierNorm00_const_param_le |θ| κ) _
    _ = _ := by simp only [cutoffMultiplierConstant, mul_assoc, mul_comm, mul_left_comm]

theorem mixedFourierNorm00_mul_cutoff_lt_top {r : ℕ} {V : Type*} (θ : ℝ)
    {F : (Fin r → ℝ) → V → ℂ} {κ : (Fin r → ℝ) → ℂ}
    (hF : mixedFourierNorm00 θ F < ⊤) (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    mixedFourierNorm00 θ (fun t v => F t v * κ t) < ⊤ :=
  (mixedFourierNorm00_mul_cutoff_le θ hF hκ hs).trans_lt
    (ENNReal.mul_lt_top (cutoffMultiplierConstant_lt_top θ hκ hs) hF)

/-- The same cutoff estimate supplies a pointwise agreeing restricted extension. -/
theorem mixedRestrictionNorm00_mul_cutoff_le {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) {F : (Fin r → ℝ) → V → ℂ} {κ : (Fin r → ℝ) → ℂ}
    (hF : mixedFourierNorm00 θ F < ⊤) (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v * κ t) ≤
      cutoffMultiplierConstant θ κ * mixedFourierNorm00 θ F :=
  (mixedRestrictionNorm00_le θ B K (fun t v => F t v * κ t)).trans
    (mixedFourierNorm00_mul_cutoff_le θ hF hκ hs)

end WaveTurbulence.Fourier
