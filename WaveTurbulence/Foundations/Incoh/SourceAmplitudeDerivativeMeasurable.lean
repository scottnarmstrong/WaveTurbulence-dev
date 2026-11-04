/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAmplitudeDerivative

/-! # Actual source amplitude derivative continuity in spectral variables -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Exact actual derivative formula separating the computed frequency and source coefficient. -/
theorem MomentumTreeData.iteratedFDeriv_sourceSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (j : ℕ) :
    iteratedFDeriv ℝ j (fun k => P.sourceSpectralAmplitude ζ f c z k ξ) k =
      P.sourceSpectralAmplitude ζ f c z 0 ξ •
        iteratedFDeriv ℝ j (fun k : Mom d =>
          (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ)) k := by
  rw [P.sourceSpectralAmplitude_eq_const_modulation,
    iteratedFDeriv_const_smul_apply' ((contDiff_momentumModulation (P.spectralShift ξ none)).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  simp only [sourceSpectralAmplitude, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

/-- The actual operator derivatives have the joint spectral measurability needed by dominated
parameter differentiation, derived from finite source input smoothness. -/
theorem MomentumTreeData.continuous_spectral_sourceAmplitudeDerivative {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) (j : ℕ) :
    Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      iteratedFDeriv ℝ j (fun k => P.sourceSpectralAmplitude ζ f c z k ξ) k) := by
  simp_rw [P.iteratedFDeriv_sourceSpectralAmplitude]
  exact (P.continuous_sourceSpectralAmplitude ζ f c z hK hB h 0).smul
    ((continuous_iteratedFDeriv_momentumModulation_frequency k j).comp (P.continuous_spectralShift none))

end WaveTurbulence.Incoh
