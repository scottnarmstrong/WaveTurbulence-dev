/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS3.MinkAux

/-! # The output modulation `e^{πi ν·tt}` costs `2^{|θ|} ⟨ν/2⟩^{|θ|}` in the restriction norm -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

variable {V : Type*}

theorem outFactor_eq_fourierChar (ν tt : Fin 3 → ℝ) :
    outFactor ν tt = (Real.fourierChar (timePairing 3 tt (fun c => ν c / 2)) : ℂ) := by
  unfold outFactor
  rw [Real.fourierChar_apply]
  congr 1
  have : timePairing 3 tt (fun c => ν c / 2) = ∑ c, ν c * tt c / 2 := by
    show ∑ i, tt i * (ν i / 2) = _
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  push_cast
  rw [← Finset.sum_div]
  ring

/-- Output modulation in `XNorm00`. -/
theorem XNorm00_outFactor_le (θ : ℝ) (ν : Fin 3 → ℝ) (G : (Fin 3 → ℝ) → V → ℂ) :
    XNorm00 θ (fun t v => outFactor ν t * G t v) ≤
      ENNReal.ofReal (2 ^ |θ|) * timeWeight |θ| (fun c => ν c / 2) * XNorm00 θ G := by
  have := SumintSigned.XNorm00_modulate_le_abs θ G (fun c => ν c / 2)
  refine le_trans (le_of_eq ?_) this
  congr 1
  funext t v
  rw [outFactor_eq_fourierChar, Circle.smul_def, smul_eq_mul]

theorem XNorm00Restr_outFactor_le (θ : ℝ) (ν : Fin 3 → ℝ) (B : Set (Fin 3 → ℝ)) (K : Set V)
    (f : (Fin 3 → ℝ) → V → ℂ) :
    XNorm00Restr θ B K (fun t v => outFactor ν t * f t v) ≤
      ENNReal.ofReal (2 ^ |θ|) * timeWeight |θ| (fun c => ν c / 2) * XNorm00Restr θ B K f := by
  set c := ENNReal.ofReal (2 ^ |θ|) * timeWeight |θ| (fun c => ν c / 2) with hc
  have h0 : c ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (timeBracket_pos _) _))
  have htop : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  unfold XNorm00Restr
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hag => ?_
  refine le_trans (iInf₂_le (fun t v => outFactor ν t * G t v) fun t ht v hv => ?_)
    (XNorm00_outFactor_le θ ν G)
  show outFactor ν t * G t v = outFactor ν t * f t v
  rw [hag t ht v hv]

end WaveTurbulence.VineEstS3.Eng
