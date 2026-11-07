/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS00

/-! # W6, vector-variable version: the sup-norm bound `∑_m ⟨m/2⟩^θ sup_v |c_m(v)| ≤ C ‖G‖_{𝔛^{θ,0,0}}` -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier MeasureTheory
open scoped ENNReal

variable {r : ℕ} {V : Type*}

theorem XNorm00_eq_lintegral {θ : ℝ} {G : (Fin r → ℝ) → V → ℂ} (h : ∀ v, Integrable fun t => G t v) :
    XNorm00 θ G = ∫⁻ lam, maxBracketPow θ lam * mixedFourierEnvelope00 G lam := by
  have := NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G
  rw [this, mixedFourierNorm00_eq_lintegral h]
  simp_rw [NormBridgeScratch.maxBracketPow_eq_timeWeight]

theorem iSup_enorm_coeff00_le (q : Fin r → ℝ) (G : (Fin r → ℝ) → V → ℂ) (m : Fin r → ℤ) :
    ⨆ v, ‖coeff00 q G m v‖ₑ ≤
      ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * mixedFourierEnvelope00 G lam := by
  refine iSup_le fun v => ?_
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun lam => ?_)
  rw [enorm_mul, ofReal_norm, NormBridgeScratch.timeFT_eq_timeFourier]
  exact mul_le_mul_right (le_iSup (fun v => ‖timeFourier (fun t => G t v) lam‖ₑ) v) _

/-- **The sup-norms of the Fourier-series coefficients are summable.** -/
theorem tsum_iSup_coeff00_le {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Fin r → ℝ) (G : (Fin r → ℝ) → V → ℂ), XNorm00 θ G < ⊤ →
      ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ⨆ v, ‖coeff00 q G m v‖ₑ ≤
        ENNReal.ofReal C * XNorm00 θ G := by
  obtain ⟨C, hC, hCb⟩ := weight_kern_tsum_le (r := r) hθ
  refine ⟨C, hC, fun q G hG => ?_⟩
  have hint : ∀ v, Integrable fun t => G t v := fun v => by
    refine integrable_of_mixedFourierNorm00_lt_top (θ := θ) ?_ v
    rwa [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  have hwm : Measurable (mixedFourierEnvelope00 G) := measurable_mixedFourierEnvelope00 hint
  set E := mixedFourierEnvelope00 G with hE
  have hw : ∀ m : Fin r → ℤ, maxBracketPow θ (half m) ≠ ⊤ := fun m => ENNReal.ofReal_ne_top
  calc ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ⨆ v, ‖coeff00 q G m v‖ₑ
      ≤ ∑' m : Fin r → ℤ, maxBracketPow θ (half m) *
          ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * E lam :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul_right (iSup_enorm_coeff00_le q G m) _
    _ = ∑' m : Fin r → ℤ, ∫⁻ lam, (maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) * E lam := by
        refine tsum_congr fun m => ?_
        rw [← lintegral_const_mul' _ _ (hw m)]
        simp_rw [mul_assoc]
    _ = ∫⁻ lam, ∑' m : Fin r → ℤ, (maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) * E lam := by
        rw [lintegral_tsum]
        intro m
        exact ((((continuous_kern q m).measurable.norm.ennreal_ofReal).const_mul _).mul hwm).aemeasurable
    _ ≤ ∫⁻ lam, ENNReal.ofReal C * (maxBracketPow θ lam * E lam) := by
        refine lintegral_mono fun lam => ?_
        rw [ENNReal.tsum_mul_right, ← mul_assoc]
        exact mul_le_mul_left (hCb q lam) _
    _ = ENNReal.ofReal C * XNorm00 θ G := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, XNorm00_eq_lintegral hint]

end WaveTurbulence.RepAnalytic
