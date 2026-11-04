/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialRawNorm

/-!
# Native interval and middle-time masks of the first bad core

The three-coordinate change of variables preserves the literal source
intervals and the case-(a) strip; no ordering gain is discarded here.
-/

public section
open MeasureTheory Set
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The native time labels of a first bad core in pair-outer, pair-inner, linear order. -/
@[expose] def sourceSpecialTime {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Fin 3 → D.S.TVar :=
  ![.inl ⟨a.1,a.2.succ⟩,.inr (.inl a),.inl ⟨a.1,0⟩]

/-- The chosen special coordinate retains its literal native input time. -/
theorem sourceSpecialCoordinate_time {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) (j : Fin 3) :
    sourceCoreCoordinateTimeEquiv D ⟨.inl a.1,sourceSpecialCoordinate D a ha j⟩ = sourceSpecialTime D a j := by
  fin_cases j <;> rfl

/-- The original core box becomes precisely its three literal native time intervals. -/
theorem sourceSpecialCoreGrouping_mem_box {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (c h : ℝ) (z : Fin 3 → ℝ) :
    (sourceSpecialCoreGrouping D a ha).symm z ∈ sourceCoreTimeBox D c h (.inl a.1) ↔
      z ∈ Icc (fun j => enlargedTimeLower D c h (sourceSpecialTime D a j))
        (fun j => enlargedTimeUpper D c h (sourceSpecialTime D a j)) := by
  constructor
  · intro hz
    constructor <;> intro j
    · have hj := hz (sourceSpecialCoordinate D a ha j) (Set.mem_univ _)
      simp only [sourceSpecialCoreGrouping_symm_coordinate,sourceSpecialCoordinate_time] at hj
      exact hj.1
    · have hj := hz (sourceSpecialCoordinate D a ha j) (Set.mem_univ _)
      simp only [sourceSpecialCoreGrouping_symm_coordinate,sourceSpecialCoordinate_time] at hj
      exact hj.2
  · intro hz j _
    obtain ⟨k,rfl⟩ := sourceSpecialCoordinate_surjective D a ha j
    simp only [sourceSpecialCoreGrouping_symm_coordinate,sourceSpecialCoordinate_time]
    exact ⟨hz.1 k,hz.2 k⟩

/-- The native reconstruction of the grouped first bad core restores its three actual input times. -/
theorem sourceSpecialCoreLocalInput_time {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : Fin 3 → ℝ) (j : Fin 3) :
    sourceCoreLocalInput D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) (sourceSpecialTime D a j) = z j := by
  have hh := sourceSpecialCoreGrouping_symm_coordinate D a ha z j
  fin_cases j
  · exact (sourceCoreLocalInput_factorCoordinate D (.inl a.1) _ (.inr (.inl a))
      (by simp only [sourceCoreGroup,ite_eq_left ha]) 0).trans hh
  · exact (sourceCoreLocalInput_factorCoordinate D (.inl a.1) _ (.inr (.inl a))
      (by simp only [sourceCoreGroup,ite_eq_left ha]) 1).trans hh
  · exact (sourceCoreLocalInput_factorCoordinate D (.inl a.1) _ (.inl a.1) rfl 0).trans hh

/-- The retained actual case-(a) ordering mask implies exactly the native three-time strip. -/
theorem sourceSpecialCoreOrdering_strip {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : Fin 3 → ℝ) (hz : sourceCoreOrdering D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z))
    (hca : caseAPair D a) : |z 0-z 2| ≤ |z 0-z 1| := by
  have hs := hz a hca (by simp only [sourceCoreGroup,ite_eq_left ha])
  change |sourceCoreLocalInput D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) (sourceSpecialTime D a 0)-
    sourceCoreLocalInput D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) (sourceSpecialTime D a 2)| ≤
      |sourceCoreLocalInput D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) (sourceSpecialTime D a 0)-
        sourceCoreLocalInput D (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) (sourceSpecialTime D a 1)| at hs
  simpa only [sourceSpecialCoreLocalInput_time] using hs

end WaveTurbulence.Sumint
