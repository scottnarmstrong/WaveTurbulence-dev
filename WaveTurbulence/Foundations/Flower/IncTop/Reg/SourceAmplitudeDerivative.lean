/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumModulation
public import WaveTurbulence.Foundations.Incoh.SourceRootFrequency
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAmplitudeIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceAmplitudeDerivative` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual spatial derivatives of the source spectral amplitude

TARGET Proposition 5.1 Step (1). The garden sign is retained. Root
frequency moments consume only the finite derivatives of each leaf input.
-/

public section
noncomputable section
open WithLp
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual root dependence is a fixed scalar times the literal modulation. -/
theorem MomentumTreeData.sourceSpectralAmplitude_eq_const_modulationSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) =
      fun k => ((ζ : ℂ) * localizedSpectralCoefficient f c z ξ) •
        (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ) := by
  funext k
  simp only [sourceSpectralAmplitudeSpatial, smul_eq_mul]
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The full actual momentum amplitude is smooth, with no extra smoothness assumption on inputs. -/
theorem MomentumTreeData.contDiff_sourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ContDiff ℝ ∞ (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) := by
  rw [(MomentumTreeData.sourceSpectralAmplitude_eq_const_modulationSpatial (P := P))]
  exact (contDiff_momentumModulation (P.spectralShift ξ none)).const_smul _

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The exact garden/coefficient scalar has the parameter-independent reference norm. -/
theorem MomentumTreeData.norm_sourceSpectralCoefficientSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ‖(ζ : ℂ) * localizedSpectralCoefficient f c z ξ‖ = ‖localizedSpectralReference (n := n) f c ξ‖ := by
  have h := congrArg ENNReal.toReal ((MomentumTreeData.enorm_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z 0 ξ)
  simpa only [toReal_enorm, sourceSpectralAmplitudeSpatial, inner_zero_right, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one] using h

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual momentum derivatives are bounded by individual leaf Fourier moments. -/
theorem MomentumTreeData.norm_iteratedFDeriv_sourceSpectralAmplitude_leSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k‖ ≤
      (2 * Real.pi) ^ j * (∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ j) *
        ‖localizedSpectralReference (n := n) f c ξ‖ := by
  rw [(MomentumTreeData.sourceSpectralAmplitude_eq_const_modulationSpatial (P := P)),
    iteratedFDeriv_const_smul_apply' ((contDiff_momentumModulation (P.spectralShift ξ none)).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    norm_smul, (MomentumTreeData.norm_sourceSpectralCoefficientSpatial (P := P))]
  calc
    _ ≤ ‖localizedSpectralReference (n := n) f c ξ‖ *
        ((2 * Real.pi) ^ j * ‖P.spectralShift ξ none‖ ^ j) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_momentumModulation_le _ k j) (norm_nonneg _)
    _ ≤ ‖localizedSpectralReference (n := n) f c ξ‖ *
        ((2 * Real.pi) ^ j * ∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (P.norm_spectralShift_none_pow_le ξ j) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

end WaveTurbulence.Flower.IncTop