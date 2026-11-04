/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumModulation
public import WaveTurbulence.Foundations.Incoh.SourceRootFrequency
public import WaveTurbulence.Foundations.Incoh.SourceAmplitudeIntegrability

/-! # Actual spatial derivatives of the source spectral amplitude

TARGET Proposition 5.1 Step (1). The garden sign is retained. Root
frequency moments consume only the finite derivatives of each leaf input.
-/

public section
noncomputable section
open WithLp
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The actual root dependence is a fixed scalar times the literal modulation. -/
theorem MomentumTreeData.sourceSpectralAmplitude_eq_const_modulation {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    (fun k => P.sourceSpectralAmplitude ζ f c z k ξ) =
      fun k => ((ζ : ℂ) * localizedSpectralCoefficient f c z ξ) •
        (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ) := by
  funext k
  simp only [sourceSpectralAmplitude, smul_eq_mul]
  ring

/-- The full actual momentum amplitude is smooth, with no extra smoothness assumption on inputs. -/
theorem MomentumTreeData.contDiff_sourceSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ContDiff ℝ ∞ (fun k => P.sourceSpectralAmplitude ζ f c z k ξ) := by
  rw [P.sourceSpectralAmplitude_eq_const_modulation]
  exact (contDiff_momentumModulation (P.spectralShift ξ none)).const_smul _

/-- The exact garden/coefficient scalar has the parameter-independent reference norm. -/
theorem MomentumTreeData.norm_sourceSpectralCoefficient {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ‖(ζ : ℂ) * localizedSpectralCoefficient f c z ξ‖ = ‖localizedSpectralReference (n := n) f c ξ‖ := by
  have h := congrArg ENNReal.toReal (P.enorm_sourceSpectralAmplitude ζ f c z 0 ξ)
  simpa only [toReal_enorm, sourceSpectralAmplitude, inner_zero_right, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one] using h

/-- Actual momentum derivatives are bounded by individual leaf Fourier moments. -/
theorem MomentumTreeData.norm_iteratedFDeriv_sourceSpectralAmplitude_le {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun k => P.sourceSpectralAmplitude ζ f c z k ξ) k‖ ≤
      (2 * Real.pi) ^ j * (∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ j) *
        ‖localizedSpectralReference (n := n) f c ξ‖ := by
  rw [P.sourceSpectralAmplitude_eq_const_modulation,
    iteratedFDeriv_const_smul_apply' ((contDiff_momentumModulation (P.spectralShift ξ none)).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    norm_smul, P.norm_sourceSpectralCoefficient]
  calc
    _ ≤ ‖localizedSpectralReference (n := n) f c ξ‖ *
        ((2 * Real.pi) ^ j * ‖P.spectralShift ξ none‖ ^ j) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_momentumModulation_le _ k j) (norm_nonneg _)
    _ ≤ ‖localizedSpectralReference (n := n) f c ξ‖ *
        ((2 * Real.pi) ^ j * ∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (P.norm_spectralShift_none_pow_le ξ j) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

end WaveTurbulence.Incoh
