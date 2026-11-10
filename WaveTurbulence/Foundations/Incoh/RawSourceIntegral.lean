/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence
public import WaveTurbulence.Foundations.Incoh.SourceTemporalPhase
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The literal unlocalized source lattice/time operator

TARGET (incohproof2–3). Actual input spatial bounds give absolute lattice
convergence and continuous time dependence before integrating the source
domain. The coupling normalization and global garden sign are retained.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The raw source lattice series, before any smooth localization. -/
@[expose] def MomentumTreeData.sourceTimeIntegrand {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhase L γ δ Q p t *
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

/-- The original unlocalized normalized lattice/time source operator. -/
@[expose] def MomentumTreeData.sourceIntegral {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) * ∫ t in I, P.sourceTimeIntegrand ζ L γ δ Q f k t

end WaveTurbulence.Incoh
