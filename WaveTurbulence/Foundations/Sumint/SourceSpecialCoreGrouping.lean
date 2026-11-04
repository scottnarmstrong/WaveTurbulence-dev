/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialCoreCoordinates
public import WaveTurbulence.Foundations.Sumint.SourceCoreLocalInput

/-!
# Measure-preserving native three-time coordinates for a first bad core

The three coordinates remain the literal pair outer, pair inner and
linear times. The explicit grouping preserves volume and permits the
existing triple-time Fubini estimate to apply unchanged.
-/

public section
open MeasureTheory
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The exact three-coordinate index equivalence for a first bad core. -/
@[expose] noncomputable def sourceSpecialCoordinateEquiv {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    Fin 3 ≃ SourceCoreCoordinate D (.inl a.1) :=
  Equiv.ofBijective (sourceSpecialCoordinate D a ha)
    ⟨sourceSpecialCoordinate_injective D a ha,sourceSpecialCoordinate_surjective D a ha⟩

/-- Read a first bad core in pair-outer, pair-inner, linear order. -/
@[expose] noncomputable def sourceSpecialCoreGrouping {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    (SourceCoreCoordinate D (.inl a.1) → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (sourceSpecialCoordinateEquiv D a ha).symm

/-- First bad core coordinates preserve the native volume. -/
theorem volume_preserving_sourceSpecialCoreGrouping {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    MeasurePreserving (sourceSpecialCoreGrouping D a ha) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℝ) (sourceSpecialCoordinateEquiv D a ha).symm

/-- Every grouped first bad coordinate reads its literal local input coordinate. -/
theorem sourceSpecialCoreGrouping_apply {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : SourceCoreCoordinate D (.inl a.1) → ℝ) (j : Fin 3) :
    sourceSpecialCoreGrouping D a ha z j = z (sourceSpecialCoordinate D a ha j) := by
  let e := sourceSpecialCoordinateEquiv D a ha
  have he := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin 3 => ℝ) e.symm z (e j)
  rw [Equiv.symm_apply_apply] at he
  exact he.trans (congrArg z (show e j = sourceSpecialCoordinate D a ha j from rfl))

/-- The inverse grouping restores each of the exact three local source coordinates. -/
theorem sourceSpecialCoreGrouping_symm_coordinate {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : Fin 3 → ℝ) (j : Fin 3) :
    (sourceSpecialCoreGrouping D a ha).symm z (sourceSpecialCoordinate D a ha j) = z j := by
  have he := sourceSpecialCoreGrouping_apply D a ha ((sourceSpecialCoreGrouping D a ha).symm z) j
  rw [MeasurableEquiv.apply_symm_apply] at he
  exact he.symm

/-- The grouped inverse restores the old pair vector in its original coordinate order. -/
theorem sourceSpecialCoreGrouping_symm_pair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : Fin 3 → ℝ) :
    sourceCoreOldTimes D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z)
      ⟨.inr (.inl a),by simp only [sourceCoreGroup,ite_eq_left ha]⟩ = ![z 0,z 1] := by
  funext j
  fin_cases j
  · exact sourceSpecialCoreGrouping_symm_coordinate D a ha z 0
  · exact sourceSpecialCoreGrouping_symm_coordinate D a ha z 1

/-- The grouped inverse restores the old distinguished linear coordinate. -/
theorem sourceSpecialCoreGrouping_symm_linear {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : Fin 3 → ℝ) :
    sourceCoreOldTimes D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z)
      ⟨.inl a.1,rfl⟩ = fun _ => z 2 := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact sourceSpecialCoreGrouping_symm_coordinate D a ha z 2

end WaveTurbulence.Sumint
