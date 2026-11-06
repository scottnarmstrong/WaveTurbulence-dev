/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedMatrix.J0II002
public import WaveTurbulenceVineParam.VineParamIntegerRowCheck
public import WaveTurbulenceVineParam.VineParamNormalizedBaseShape
public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
import Mathlib.Tactic

/-! # Full finite normalized certificate for vine II, profile 2, joint 0

All source indexing, physical origins and signed phase identities are checked
here as finite integer/combinatorial statements, independently of momenta.
Unused bad-vine core data use the canonical false/unit/zero convention.
-/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J0II002
open Finset VineParamContract

/-- The exact pinned base shape, including II at m=1. -/
@[expose] def shape : Shape .II := normalizedBaseShape .II

/-- Actual included atoms in reference/x/y/core contract order. -/
@[expose] def atomVector : Fin 3 → Fin 4 := fun i => if i.1 < 1 then (0) else (if i.1 < 2 then (2) else (3))

/-- Every actual included atom differs from the excluded joint. -/
theorem atomVector_ne : ∀ i,atomVector i ≠ (1 : Fin 4) := by decide

/-- Explicit actual included-atom bijection. -/
@[expose] noncomputable def atomEquiv : Fin 3 ≃ {v : Fin 4 // v ≠ (1 : Fin 4)} :=
  Equiv.ofBijective (fun i => ⟨atomVector i,atomVector_ne i⟩) (by decide)

/-- The actual physical two-occurrence joint row. -/
@[expose] noncomputable def jointRow : DirectedJointRow integerChart.ends integerChart.b where
  outgoing := 0
  incoming := 1
  distinct := by decide
  outgoing_at := by decide
  incoming_at := by decide
  row := by decide

/-- Actual ordered bond origins of the nonreference coordinates. -/
@[expose] def differencePairs : Fin 2 → Fin 6×Fin 6 := fun i => if i.1 < 1 then (((5 : Fin 6),(3 : Fin 6))) else (((2 : Fin 6),(3 : Fin 6)))

/-- The same origins indexed by the exact public nonreference domain. -/
@[expose] def differencePair (i : {i : Fin shape.n // i ≠ shape.x0}) : Fin (2*shape.n)×Fin (2*shape.n) := by
  have hv : i.1.1<3 := i.1.2
  have hn : i.1.1 ≠ 0 := by intro h; apply i.2; exact Fin.ext h
  exact differencePairs ⟨i.1.1-1,by omega⟩

/-- Actual paired phase correction coefficients. -/
@[expose] def zeta : Fin shape.m → Fin 3 → ℤ := fun _j c => if c.1 < 1 then (0) else (if c.1 < 2 then (1) else (0))

/-- Actual normal-core correction coefficients (zero for bad vines). -/
@[expose] def xi : Fin 4 → ℤ := fun i => if i.1 < 2 then (if i.1 < 1 then (0) else (0)) else (if i.1 < 3 then (0) else (0))

/-- Common actual core phase sign. -/
@[expose] def sigma : ℤˣ := 1

/-- Relative nonlinear sign in the owner-approved F79 convention. -/
@[expose] def tau : ℤˣ := 1

/-- Which of the two actual source core alternatives occurs. -/
@[expose] def coreIsLinear : Bool := false

private theorem rung0_s_row_0 : ∀ j : Fin 4,(integerChart.phaseMatrix (3 : Fin 4)) (0 : Fin 4) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (3 : Fin 4)) (0 : Fin 4) j)
    (fun j : Fin 4 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 0 j) (by decide)
private theorem rung0_s_row_1 : ∀ j : Fin 4,(integerChart.phaseMatrix (3 : Fin 4)) (1 : Fin 4) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (3 : Fin 4)) (1 : Fin 4) j)
    (fun j : Fin 4 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 1 j) (by decide)
private theorem rung0_s_row_2 : ∀ j : Fin 4,(integerChart.phaseMatrix (3 : Fin 4)) (2 : Fin 4) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (3 : Fin 4)) (2 : Fin 4) j)
    (fun j : Fin 4 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 2 j) (by decide)
private theorem rung0_s_row_3 : ∀ j : Fin 4,(integerChart.phaseMatrix (3 : Fin 4)) (3 : Fin 4) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (3 : Fin 4)) (3 : Fin 4) j)
    (fun j : Fin 4 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 3 j) (by decide)

/-- Exact finite integer source phase certificate. -/
theorem rung0_s : integerChart.phaseMatrix (3 : Fin 4)=-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m)))) := by
  funext i j
  fin_cases i
  · exact rung0_s_row_0 j
  · exact rung0_s_row_1 j
  · exact rung0_s_row_2 j
  · exact rung0_s_row_3 j

private theorem rung0_sum_row_0 : ∀ j : Fin 4,(integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (0 : Fin 4) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (0 : Fin 4) j)
    (fun j : Fin 4 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j) (by decide)
private theorem rung0_sum_row_1 : ∀ j : Fin 4,(integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (1 : Fin 4) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (1 : Fin 4) j)
    (fun j : Fin 4 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j) (by decide)
private theorem rung0_sum_row_2 : ∀ j : Fin 4,(integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (2 : Fin 4) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (2 : Fin 4) j)
    (fun j : Fin 4 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j) (by decide)
private theorem rung0_sum_row_3 : ∀ j : Fin 4,(integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (3 : Fin 4) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 4 => (integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)) (3 : Fin 4) j)
    (fun j : Fin 4 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j) (by decide)

/-- Exact finite integer source phase certificate. -/
theorem rung0_sum : integerChart.phaseMatrix (2 : Fin 4)+integerChart.phaseMatrix (3 : Fin 4)=intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape) := by
  funext i j
  fin_cases i
  · exact rung0_sum_row_0 j
  · exact rung0_sum_row_1 j
  · exact rung0_sum_row_2 j
  · exact rung0_sum_row_3 j

/-- The full concrete normalized source certificate, with no input certificate premise. -/
@[expose] noncomputable def certificate : NormalizedVineCertificate .II where
  shape := shape
  matrix := integerChart
  atom := atomEquiv
  lower := by decide
  joint := jointRow
  reference_row := by decide
  differencePair := differencePair
  difference_rows := by decide
  junction := none
  junction_type := by decide
  rung_bonds := by decide
  ζ := zeta
  ζ_unit := by unfold UnitCoeff; decide
  ζ_bad_nonzero := by intro _; decide
  coreLinear := coreIsLinear
  coreFirstSign := sigma
  coreSign := tau
  ξ := xi
  ξ_unit := by unfold UnitCoeff; decide
  rung_s_matrix := by
    intro j
    change Fin 1 at j
    fin_cases j
    · exact rung0_s
  rung_sum_matrix := by
    intro j
    change Fin 1 at j
    fin_cases j
    · exact rung0_sum
  core_first_matrix := by intro h; cases h
  core_second_matrix := by intro h; cases h
  core_sum_matrix := by intro h; cases h

end WaveTurbulence.Vine.Param.Normalized.J0II002
