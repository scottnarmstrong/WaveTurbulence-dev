/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreMeasure
public import WaveTurbulence.Foundations.SumintPar.SourceFactorRegularity

/-!
# Native reconstruction from one coarse source core

Inserting a local core and setting all other cores to zero is a
measurable operation. Every old factor coordinate belonging to that
core is restored at its literal input time. These identities keep
local core functions tied to the original source carrier.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Insert one coarse core into the actual native input-time vector. -/
@[expose] noncomputable def sourceCoreLocalInput {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b → ℝ) : D.S.TVar → ℝ :=
  (sourceCoreTimeGrouping D).symm (Pi.single b z)

/-- A local old-factor time vector is the corresponding projection of its containing coarse core. -/
@[expose] def sourceCoreOldTimes {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b → ℝ) (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) :
    FactorCoordinate D.S a.1 → ℝ := fun j => z ⟨a,j⟩

/-- Native reconstruction from a coarse local input is measurable. -/
theorem measurable_sourceCoreLocalInput {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    Measurable (sourceCoreLocalInput D b) := by
  apply (sourceCoreTimeGrouping D).symm.measurable.comp
  apply measurable_pi_iff.mpr
  intro c
  by_cases h : c = b
  · subst c
    have he : (fun z : SourceCoreCoordinate D b → ℝ =>
        (Pi.single b z : (c : FactorIdx D.S) → SourceCoreCoordinate D c → ℝ) b) = id := by
      funext z
      simp only [Pi.single_eq_same,id_eq]
    rw [he]
    exact measurable_id
  · have he : (fun z : SourceCoreCoordinate D b → ℝ =>
        (Pi.single b z : (c : FactorIdx D.S) → SourceCoreCoordinate D c → ℝ) c) = fun _ => 0 := by
      funext z
      simp [h]
    rw [he]
    exact measurable_const

/-- Reconstructed native times agree with every old coordinate in the inserted coarse core. -/
theorem sourceCoreLocalInput_factorCoordinate {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b → ℝ) (a : FactorIdx D.S) (ha : sourceCoreGroup D a = b)
    (j : FactorCoordinate D.S a) :
    sourceCoreLocalInput D b z (factorCoordinateTime D.S ⟨a,j⟩) = z ⟨⟨a,ha⟩,j⟩ := by
  have he := sourceCoreTimeGrouping_apply D (sourceCoreLocalInput D b z) b a ha j
  change (sourceCoreTimeGrouping D ((sourceCoreTimeGrouping D).symm
    (Pi.single b z : (c : FactorIdx D.S) → SourceCoreCoordinate D c → ℝ))) b ⟨⟨a,ha⟩,j⟩ = _ at he
  rw [MeasurableEquiv.apply_symm_apply,Pi.single_eq_same] at he
  exact he.symm

/-- Projecting old factor times from an actual grouped vector restores the actual old factor-time function. -/
theorem sourceCoreOldTimes_grouped {d : ℕ} (D : SumintDatum d) (u : D.S.TVar → ℝ)
    (b : FactorIdx D.S) (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) :
    sourceCoreOldTimes D b (sourceCoreTimeGrouping D u b) a =
      fun j => u (factorCoordinateTime D.S ⟨a.1,j⟩) := by
  funext j
  exact sourceCoreTimeGrouping_apply D u b a.1 a.2 j

end WaveTurbulence.SumintPar
