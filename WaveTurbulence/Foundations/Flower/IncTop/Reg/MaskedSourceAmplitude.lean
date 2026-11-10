/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceRootMaskBounds
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAmplitudeDerivative
public import WaveTurbulence.Foundations.Incoh.ParameterIteratedDerivative
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedSourceAmplitude` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual smooth root-masked source spectral amplitudes -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual source spectral amplitude with the fixed leaf-center root mask. -/
@[expose] def MomentumTreeData.maskedSourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  sourceRootMask c k * (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual masked amplitude remains smooth at every momentum. -/
theorem MomentumTreeData.contDiff_maskedSourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ContDiff ℝ ∞ (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) :=
  (contDiff_sourceRootMask c).mul ((MomentumTreeData.contDiff_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z ξ)

end WaveTurbulence.Flower.IncTop