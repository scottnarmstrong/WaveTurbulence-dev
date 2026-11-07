/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.Fourier.TimeBasic
import Mathlib.Tactic

/-!
# Modulation costs for the exact general-output Fourier norm

The absolute regularity exponent is retained in the frequency-shift cost.
This is essential for the negative endpoint in sumint Step 3.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintSigned

/-- The pointwise output Fourier envelope shifts under a common time modulation. -/
theorem mixedEnvelope_modulate {r : ℕ} {V : Type*} (F : (Fin r → ℝ) → V → ℂ)
    (a ξ : Fin r → ℝ) :
    Fourier.mixedFourierEnvelope00 (fun t v => Real.fourierChar (Fourier.timePairing r t a) • F t v) ξ =
      Fourier.mixedFourierEnvelope00 F (ξ-a) := by
  unfold Fourier.mixedFourierEnvelope00
  apply iSup_congr
  intro v
  exact congrArg (fun z : ℂ => ‖z‖ₑ) (congrFun (Fourier.timeFourier_modulate (fun t => F t v) a) ξ)

/-- Common modulation costs the absolute-regularity frequency weight, including at negative regularity. -/
theorem mixedFourierNorm00_modulate_le_abs {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (a : Fin r → ℝ) :
    Fourier.mixedFourierNorm00 θ (fun t v => Real.fourierChar (Fourier.timePairing r t a) • F t v) ≤
      ENNReal.ofReal (2^|θ|) * Fourier.timeWeight |θ| a * Fourier.mixedFourierNorm00 θ F := by
  classical
  have hc : Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => Fourier.timePairing r p.1 p.2) := by
    change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
    fun_prop
  have hi (v : V) :
      Integrable (fun t => Real.fourierChar (Fourier.timePairing r t a) • F t v) ↔
        Integrable (fun t => F t v) := by
    simpa only [map_neg, neg_neg] using VectorFourier.fourierIntegral_convergent_iff
      Real.continuous_fourierChar hc (-a)
      (f := fun t => F t v) (μ := volume)
  have hiall : (∀ v, Integrable (fun t => Real.fourierChar (Fourier.timePairing r t a) • F t v)) ↔
      (∀ v, Integrable (fun t => F t v)) := forall_congr' hi
  have hK : ENNReal.ofReal (2^|θ|) * Fourier.timeWeight |θ| a ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Fourier.timeBracket_pos a) _))
  unfold Fourier.mixedFourierNorm00
  rw [hiall]
  split_ifs with hF
  · simp_rw [mixedEnvelope_modulate]
    have hs := lintegral_add_right_eq_self (μ := (volume : Measure (Fin r → ℝ)))
      (fun ξ => Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 F (ξ-a)) a
    rw [← hs]
    simp only [add_sub_cancel_right]
    calc
      _ ≤ ∫⁻ ξ, (ENNReal.ofReal (2^|θ|) * Fourier.timeWeight |θ| a) *
          (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 F ξ) := by
        apply lintegral_mono
        intro ξ
        have h := mul_le_mul_left (Fourier.timeWeight_add_le_abs θ ξ a) (Fourier.mixedFourierEnvelope00 F ξ)
        simpa only [mul_assoc, mul_comm, mul_left_comm] using h
      _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul
        (Fourier.measurable_mixedFourierEnvelope00 hF))
  · simp only [ENNReal.mul_top hK, le_refl]

/-- The modulation bound for the exact snapshot norm, with no change of guard or supremum order. -/
theorem XNorm00_modulate_le_abs {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (a : Fin r → ℝ) :
    XNorm00 θ (fun t v => Real.fourierChar (Fourier.timePairing r t a) • F t v) ≤
      ENNReal.ofReal (2^|θ|) * Fourier.timeWeight |θ| a * XNorm00 θ F := by
  simpa only [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] using
    mixedFourierNorm00_modulate_le_abs θ F a

end WaveTurbulence.SumintSigned
