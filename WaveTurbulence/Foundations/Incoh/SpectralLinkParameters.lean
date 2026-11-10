/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization
public import WaveTurbulence.Foundations.Incoh.SourceTemporalPhase

/-!
# Computed analytic link parameters of each localized source piece

TARGET (incohproof9–10). Centers come from actual half-cells, shifts from
the transpose source momentum map, and layer/orientation data are retained.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Literal analytic link parameters induced by a cell and its Fourier variables. -/
@[expose] def MomentumTreeData.spectralLinks {d n m w : ℕ} (P : MomentumTreeData n m w)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (i : Fin n) : LayerLink d where
  leftCenter := halfCellCenter (z (i, 0))
  rightCenter := halfCellCenter (z (i, 1))
  leftShift := P.spectralShift ξ (some (i, 0))
  rightShift := P.spectralShift ξ (some (i, 1))
  leftLayer := (Q i).leftLayer
  rightLayer := (Q i).rightLayer
  orientation := (Q i).orientation

/-- Fourier localization preserves the actual incoherence flags exactly. -/
theorem MomentumTreeData.incoherenceCount_spectralLinks {d n m w : ℕ} (P : MomentumTreeData n m w)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    incoherenceCount (P.spectralLinks Q z ξ) = incoherenceCount Q := rfl

/-- The actual unshifted temporal phase, compact cutoff, and linear Fourier character combine
into precisely one analytic link summand. -/
theorem temporal_phase_mul_linear_phase {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
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

end WaveTurbulence.Incoh
