/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CoordinateCoarsening
public import WaveTurbulence.Foundations.SumintPar.FactorCounts
public import WaveTurbulence.Foundations.SumintPar.OrderedPairClasses

/-!
# Coarse independent source cores for partially fixed input times

Normal triples and first bad pairs are grouped with their distinguished
linear factor. Every other pair remains separate. Old unused labels
are retained as empty fibers, so no source coordinate is renumbered or
removed. The total coarse arity is exactly the original M.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Collapse a normal triple or a first bad pair into its distinguished linear core. -/
@[expose] noncomputable def sourceCoreGroup {d : ℕ} (D : SumintDatum d) : FactorIdx D.S → FactorIdx D.S
  | .inl i => .inl i
  | .inr (.inl a) => if caseAPair D a ∨ caseCPair D a then .inl a.1 else .inr (.inl a)
  | .inr (.inr i) => .inl i.1

/-- Grouping is idempotent: all nonempty coarse labels are already fixed by it. -/
theorem sourceCoreGroup_idempotent {d : ℕ} (D : SumintDatum d) (a : FactorIdx D.S) :
    sourceCoreGroup D (sourceCoreGroup D a) = sourceCoreGroup D a := by
  rcases a with i | (a | i)
  · rfl
  · by_cases h : caseAPair D a ∨ caseCPair D a <;> simp [sourceCoreGroup,h]
  · rfl

/-- The original local coordinates belonging to one coarse source core. -/
abbrev SourceCoreCoordinate {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) : Type :=
  CoarsenedCoordinate (sourceCoreGroup D) (FactorCoordinate D.S) b

/-- Coarse local arity, including zero for an unused old factor label. -/
@[expose] noncomputable def sourceCoreArity {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) : ℕ :=
  Fintype.card (SourceCoreCoordinate D b)

/-- Exact coordinate permutation from coarse source cores to the literal input-time carrier. -/
@[expose] noncomputable def sourceCoreCoordinateTimeEquiv {d : ℕ} (D : SumintDatum d) :
    (Σ b : FactorIdx D.S, SourceCoreCoordinate D b) ≃ D.S.TVar :=
  (coarsenedCoordinateEquiv (sourceCoreGroup D) (FactorCoordinate D.S)).trans (factorCoordinateTimeEquiv D.S)

/-- The actual time vector grouped into coarse independent source cores. -/
@[expose] noncomputable def sourceCoreTimeGrouping {d : ℕ} (D : SumintDatum d) :
    (D.S.TVar → ℝ) ≃ᵐ ((b : FactorIdx D.S) → SourceCoreCoordinate D b → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (sourceCoreCoordinateTimeEquiv D).symm).trans
    (MeasurableEquiv.piCurry (fun (b : FactorIdx D.S) (_ : SourceCoreCoordinate D b) => ℝ))

/-- Coarse grouping evaluates every old factor coordinate at its original source time. -/
theorem sourceCoreTimeGrouping_apply {d : ℕ} (D : SumintDatum d) (u : D.S.TVar → ℝ)
    (b a : FactorIdx D.S) (ha : sourceCoreGroup D a = b) (j : FactorCoordinate D.S a) :
    sourceCoreTimeGrouping D u b ⟨⟨a,ha⟩,j⟩ = u (factorCoordinateTime D.S ⟨a,j⟩) := by
  let e := sourceCoreCoordinateTimeEquiv D
  have he : e.symm (factorCoordinateTime D.S ⟨a,j⟩) = ⟨b,⟨⟨a,ha⟩,j⟩⟩ := e.symm_apply_eq.mpr rfl
  change (MeasurableEquiv.piCongrLeft (fun _ : (Σ b, SourceCoreCoordinate D b) => ℝ) e.symm u)
    ⟨b,⟨⟨a,ha⟩,j⟩⟩ = _
  rw [← he]
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : (Σ b, SourceCoreCoordinate D b) => ℝ) e.symm u (factorCoordinateTime D.S ⟨a,j⟩)

/-- The coarse arities sum to the literal source total M. -/
theorem sum_sourceCoreArity {d : ℕ} (D : SumintDatum d) :
    ∑ b : FactorIdx D.S, sourceCoreArity D b = D.S.M := by
  have hc := Fintype.card_congr (sourceCoreCoordinateTimeEquiv D)
  simpa only [Fintype.card_sigma,sourceCoreArity,card_time_index] using hc

end WaveTurbulence.SumintPar
