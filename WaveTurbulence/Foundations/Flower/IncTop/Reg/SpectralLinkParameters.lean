/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceTemporalPhase

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralLinkParameters` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Computed analytic link parameters of each localized source piece

TARGET (incohproof9–10). Centers come from actual half-cells, shifts from
the transpose source momentum map, and layer/orientation data are retained.
-/

public section
noncomputable section

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Literal analytic link parameters induced by a cell and its Fourier variables. -/
@[expose] def MomentumTreeData.spectralLinksSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (i : Fin n) : LayerLink d where
  leftCenter := halfCellCenter (z (i, 0))
  rightCenter := halfCellCenter (z (i, 1))
  leftShift := P.spectralShift ξ (some (i, 0)) + (Q i).leftShift
  rightShift := P.spectralShift ξ (some (i, 1)) + (Q i).rightShift
  leftLayer := (Q i).leftLayer
  rightLayer := (Q i).rightLayer
  orientation := (Q i).orientation

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Fourier localization preserves the actual incoherence flags exactly. -/
theorem MomentumTreeData.incoherenceCount_spectralLinksSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    incoherenceCount ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) = incoherenceCount Q := rfl

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Fourier localization preserves every literal link time box exactly. -/
theorem MomentumTreeData.linkBox_spectralLinksSpatial {d n m w : ℕ} (P : MomentumTreeData n m w)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (i : Fin n) :
    linkBox ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ i) = linkBox (Q i) := rfl

/-- The actual unshifted temporal phase, compact cutoff, and linear Fourier character combine
into precisely one analytic link summand. -/
theorem temporal_phase_mul_linear_phaseSpatial {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) (t : Fin 2 → ℝ) :
    ((linkWickFactor p.1 p.2 : ℂ) *
      WeylSums.e ((((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) *
        inner ℝ (latticePoint L p.1) (latticePoint L p.2))) *
      cutoffAmplitude L Q.toLinkParameters p *
      WeylSums.e (inner ℝ (latticePoint L p.1) Q.leftShift +
        inner ℝ (latticePoint L p.2) Q.rightShift) =
      linkAmplitude L Q.toLinkParameters p *
        WeylSums.e (linkPhase L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
          (t 0 - t 1)) Q.toLinkParameters p) := by
  unfold linkAmplitude linkPhase
  simp only [WeylSums.e_add]
  ring

end WaveTurbulence.Flower.IncTop