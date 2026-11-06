/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootMatrixEnergy
public import WaveTurbulenceVineParam.VineParamBasePhaseEvaluation
public import WaveTurbulenceVineParam.VineParamInsertedAtoms
import Mathlib.Tactic

/-! # Finite normalized vine certificates for the exact full-chart consumer

Every field is finite combinatorial data, an integer matrix identity or a
checked coefficient bound. Concrete source producers must prove all fields;
no full-vine existence or vector-valued phase conclusion is assumed here.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

/-- A free coordinate, viewed in the reduced free-plus-gap matrix. -/
@[expose] def freePhaseRow {X : VineType} (A : Shape X) (i : Fin A.n) : Fin (A.n+1) → ℤ :=
  coordinateRow i.castSucc

/-- The final reduced coordinate is the actual physical root gap. -/
@[expose] def gapPhaseRow {X : VineType} (A : Shape X) : Fin (A.n+1) → ℤ :=
  coordinateRow (Fin.last A.n)

/-- The exact integer row of a paired phase's linear correction. -/
@[expose] def pairCorrectionRow {X : VineType} (A : Shape X) (ζ : Fin A.m → Fin 3 → ℤ)
    (j : Fin A.m) : Fin (A.n+1) → ℤ := fun l =>
  ζ j 0*freePhaseRow A (A.xSlot j) l+ζ j 1*freePhaseRow A (A.ySlot j) l+ζ j 2*gapPhaseRow A l

/-- The exact integer row of the normal core's linear correction. -/
@[expose] def coreCorrectionRow {X : VineType} (A : Shape X) (hn : X.IsBad=false)
    (ξ : Fin 4 → ℤ) : Fin (A.n+1) → ℤ := fun l =>
  ξ 0*freePhaseRow A (A.uSlot hn 0) l+ξ 1*freePhaseRow A (A.uSlot hn 1) l+
    ξ 2*freePhaseRow A (A.uSlot hn 2) l+ξ 3*gapPhaseRow A l

/-- The two source core alternatives in a common signed matrix convention. -/
@[expose] def coreSecondArgumentRow {X : VineType} (A : Shape X) (hn : X.IsBad=false)
    (linear : Bool) : Fin (A.n+1) → ℤ :=
  if linear then freePhaseRow A (A.uSlot hn 0) else
    fun l => freePhaseRow A (A.uSlot hn 0) l+freePhaseRow A (A.uSlot hn 1) l-
      freePhaseRow A (A.uSlot hn 2) l

/-- Complete finite source certificate. Its integer identities will be
evaluated by a generic consumer in every momentum dimension and over the
whole root-flow fiber, producing the exact shared FullVineChart interface. -/
structure NormalizedVineCertificate (X : VineType) where
  shape : Shape X
  matrix : RootIntegerMatrix shape.n
  atom : Fin shape.n ≃ {v : Fin (shape.n+1) // v ≠ matrix.a}
  lower : (atom shape.x0).1=matrix.b
  joint : DirectedJointRow matrix.ends matrix.b
  reference_row : ∀ e,matrix.forward (matrix.freeIndex shape.x0) e= -(if e=joint.outgoing then 1 else 0)
  differencePair : {i : Fin shape.n // i ≠ shape.x0} → Fin (2*shape.n)×Fin (2*shape.n)
  difference_rows : ∀ i : {i : Fin shape.n // i ≠ shape.x0},∀ e,
    matrix.forward (matrix.freeIndex i.1) e=
      (if e=(differencePair i).1 then 1 else 0)-(if e=(differencePair i).2 then 1 else 0)
  junction : Option (Fin shape.m)
  junction_type : junction.isSome=decide (X=.VII)
  rung_bonds : ∀ j : Fin shape.m,
    (graphMolecule matrix.ends).bondsBetween (atom (shape.xSlot j)).1 (atom (shape.ySlot j)).1=
      if junction=some j then 1 else 2
  ζ : Fin shape.m → Fin 3 → ℤ
  ζ_unit : ∀ j c,UnitCoeff (ζ j c)
  ζ_bad_nonzero : X.IsBad=true → ∀ j,ζ j 0 ≠ 0 ∨ ζ j 1 ≠ 0
  coreLinear : Bool
  coreFirstSign : ℤˣ
  coreSign : ℤˣ
  ξ : Fin 4 → ℤ
  ξ_unit : ∀ c,UnitCoeff (ξ c)
  rung_s_matrix : ∀ j : Fin shape.m,
    matrix.phaseMatrix (atom (shape.ySlot j)).1=
      -(intOuter (freePhaseRow shape (shape.xSlot j)) (freePhaseRow shape (shape.ySlot j))+
        intOuter (freePhaseRow shape (shape.ySlot j)) (freePhaseRow shape (shape.xSlot j)))
  rung_sum_matrix : ∀ j : Fin shape.m,
    matrix.phaseMatrix (atom (shape.xSlot j)).1+matrix.phaseMatrix (atom (shape.ySlot j)).1=
      intOuter (gapPhaseRow shape) (pairCorrectionRow shape ζ j)+
        intOuter (pairCorrectionRow shape ζ j) (gapPhaseRow shape)
  core_first_matrix : ∀ hn : X.IsBad=false,
    matrix.phaseMatrix (atom (shape.uSlot hn 0)).1=
      fun i l => (coreFirstSign : ℤ)*
        ((intOuter (freePhaseRow shape (shape.uSlot hn 0)) (freePhaseRow shape (shape.uSlot hn 1))+
          intOuter (freePhaseRow shape (shape.uSlot hn 1)) (freePhaseRow shape (shape.uSlot hn 0))) i l)
  core_second_matrix : ∀ hn : X.IsBad=false,
    matrix.phaseMatrix (atom (shape.uSlot hn 1)).1=
      fun i l => (coreFirstSign : ℤ)*(if coreLinear then 1 else (coreSign : ℤ))*
        ((intOuter (freePhaseRow shape (shape.uSlot hn 2)) (coreSecondArgumentRow shape hn coreLinear)+
          intOuter (coreSecondArgumentRow shape hn coreLinear) (freePhaseRow shape (shape.uSlot hn 2))) i l)
  core_sum_matrix : ∀ hn : X.IsBad=false,
    (∑ c : Fin 3,matrix.phaseMatrix (atom (shape.uSlot hn c)).1)=
      intOuter (gapPhaseRow shape) (coreCorrectionRow shape hn ξ)+
        intOuter (coreCorrectionRow shape hn ξ) (gapPhaseRow shape)

end WaveTurbulence.Vine.Param
