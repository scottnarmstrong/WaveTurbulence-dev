/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedMatrix.J0VII009
public import WaveTurbulenceVineParam.VineParamIntegerRowCheck
public import WaveTurbulenceVineParam.VineParamNormalizedBaseShape
public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
import Mathlib.Tactic

/-! # Full finite normalized certificate for vine VII, profile 9, joint 0

All source indexing, physical origins and signed phase identities are checked
here as finite integer/combinatorial statements, independently of momenta.
Unused bad-vine core data use the canonical false/unit/zero convention.
-/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J0VII009
open Finset VineParamContract

/-- The exact pinned base shape, including II at m=1. -/
@[expose] def shape : Shape .VII := normalizedBaseShape .VII

/-- Actual included atoms in reference/x/y/core contract order. -/
@[expose] def atomVector : Fin 10 → Fin 11 := fun i => if i.1 < 5 then (if i.1 < 2 then (if i.1 < 1 then (0) else (2)) else (if i.1 < 3 then (9) else (if i.1 < 4 then (7) else (3)))) else (if i.1 < 7 then (if i.1 < 6 then (10) else (8)) else (if i.1 < 8 then (4) else (if i.1 < 9 then (5) else (6))))

/-- Every actual included atom differs from the excluded joint. -/
theorem atomVector_ne : ∀ i,atomVector i ≠ (1 : Fin 11) := by decide +kernel

/-- Explicit actual included-atom bijection. -/
@[expose] noncomputable def atomEquiv : Fin 10 ≃ {v : Fin 11 // v ≠ (1 : Fin 11)} :=
  Equiv.ofBijective (fun i => ⟨atomVector i,atomVector_ne i⟩) (by decide)

/-- The actual physical two-occurrence joint row. -/
@[expose] noncomputable def jointRow : DirectedJointRow integerChart.ends integerChart.b where
  outgoing := 1
  incoming := 0
  distinct := by decide
  outgoing_at := by decide
  incoming_at := by decide
  row := by decide

/-- Actual ordered bond origins of the nonreference coordinates. -/
@[expose] def differencePairs : Fin 9 → Fin 20×Fin 20 := fun i => if i.1 < 4 then (if i.1 < 2 then (if i.1 < 1 then (((15 : Fin 20),(3 : Fin 20))) else (((19 : Fin 20),(13 : Fin 20)))) else (if i.1 < 3 then (((17 : Fin 20),(19 : Fin 20))) else (((2 : Fin 20),(15 : Fin 20))))) else (if i.1 < 6 then (if i.1 < 5 then (((11 : Fin 20),(19 : Fin 20))) else (((15 : Fin 20),(17 : Fin 20)))) else (if i.1 < 7 then (((17 : Fin 20),(8 : Fin 20))) else (if i.1 < 8 then (((5 : Fin 20),(6 : Fin 20))) else (((17 : Fin 20),(5 : Fin 20))))))

/-- The same origins indexed by the exact public nonreference domain. -/
@[expose] def differencePair (i : {i : Fin shape.n // i ≠ shape.x0}) : Fin (2*shape.n)×Fin (2*shape.n) := by
  have hv : i.1.1<10 := i.1.2
  have hn : i.1.1 ≠ 0 := by intro h; apply i.2; exact Fin.ext h
  exact differencePairs ⟨i.1.1-1,by omega⟩

/-- Actual paired phase correction coefficients. -/
@[expose] def zeta : Fin shape.m → Fin 3 → ℤ := fun j c => if j.1 < 1 then (if c.1 < 1 then (-1) else (if c.1 < 2 then (1) else (-1))) else (if j.1 < 2 then (if c.1 < 1 then (1) else (if c.1 < 2 then (0) else (0))) else (if c.1 < 1 then (1) else (if c.1 < 2 then (1) else (1))))

/-- Actual normal-core correction coefficients (zero for bad vines). -/
@[expose] def xi : Fin 4 → ℤ := fun i => if i.1 < 2 then (if i.1 < 1 then (0) else (0)) else (if i.1 < 3 then (0) else (0))

/-- Common actual core phase sign. -/
@[expose] def sigma : ℤˣ := 1

/-- Relative nonlinear sign in the owner-approved F79 convention. -/
@[expose] def tau : ℤˣ := -1

/-- Which of the two actual source core alternatives occurs. -/
@[expose] def coreIsLinear : Bool := true

private theorem rung0_s_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (0 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 0 j) (by decide +kernel)
private theorem rung0_s_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (1 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 1 j) (by decide +kernel)
private theorem rung0_s_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (2 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 2 j) (by decide +kernel)
private theorem rung0_s_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (3 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 3 j) (by decide +kernel)
private theorem rung0_s_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (4 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 4 j) (by decide +kernel)
private theorem rung0_s_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (5 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 5 j) (by decide +kernel)
private theorem rung0_s_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (6 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 6 j) (by decide +kernel)
private theorem rung0_s_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (7 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 7 j) (by decide +kernel)
private theorem rung0_s_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (8 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 8 j) (by decide +kernel)
private theorem rung0_s_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (9 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 9 j) (by decide +kernel)
private theorem rung0_s_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (3 : Fin 11)) (10 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))))) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (3 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide +kernel⟩ : Fin shape.m))))) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung0_s : integerChart.phaseMatrix (3 : Fin 11)=-(intOuter (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨0,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨0,by decide⟩ : Fin shape.m)))) := by
  funext i j
  fin_cases i
  · exact rung0_s_row_0 j
  · exact rung0_s_row_1 j
  · exact rung0_s_row_2 j
  · exact rung0_s_row_3 j
  · exact rung0_s_row_4 j
  · exact rung0_s_row_5 j
  · exact rung0_s_row_6 j
  · exact rung0_s_row_7 j
  · exact rung0_s_row_8 j
  · exact rung0_s_row_9 j
  · exact rung0_s_row_10 j

private theorem rung0_sum_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (0 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j) (by decide +kernel)
private theorem rung0_sum_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (1 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j) (by decide +kernel)
private theorem rung0_sum_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (2 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j) (by decide +kernel)
private theorem rung0_sum_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (3 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j) (by decide +kernel)
private theorem rung0_sum_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (4 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j) (by decide +kernel)
private theorem rung0_sum_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (5 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j) (by decide +kernel)
private theorem rung0_sum_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (6 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j) (by decide +kernel)
private theorem rung0_sum_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (7 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j) (by decide +kernel)
private theorem rung0_sum_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (8 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j) (by decide +kernel)
private theorem rung0_sum_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (9 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j) (by decide +kernel)
private theorem rung0_sum_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (10 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung0_sum : integerChart.phaseMatrix (2 : Fin 11)+integerChart.phaseMatrix (3 : Fin 11)=intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨0,by decide⟩ : Fin shape.m)) (gapPhaseRow shape) := by
  funext i j
  fin_cases i
  · exact rung0_sum_row_0 j
  · exact rung0_sum_row_1 j
  · exact rung0_sum_row_2 j
  · exact rung0_sum_row_3 j
  · exact rung0_sum_row_4 j
  · exact rung0_sum_row_5 j
  · exact rung0_sum_row_6 j
  · exact rung0_sum_row_7 j
  · exact rung0_sum_row_8 j
  · exact rung0_sum_row_9 j
  · exact rung0_sum_row_10 j

private theorem rung1_s_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (0 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 0 j) (by decide +kernel)
private theorem rung1_s_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (1 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 1 j) (by decide +kernel)
private theorem rung1_s_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (2 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 2 j) (by decide +kernel)
private theorem rung1_s_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (3 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 3 j) (by decide +kernel)
private theorem rung1_s_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (4 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 4 j) (by decide +kernel)
private theorem rung1_s_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (5 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 5 j) (by decide +kernel)
private theorem rung1_s_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (6 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 6 j) (by decide +kernel)
private theorem rung1_s_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (7 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 7 j) (by decide +kernel)
private theorem rung1_s_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (8 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 8 j) (by decide +kernel)
private theorem rung1_s_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (9 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 9 j) (by decide +kernel)
private theorem rung1_s_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (10 : Fin 11)) (10 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))))) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (10 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide +kernel⟩ : Fin shape.m))))) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung1_s : integerChart.phaseMatrix (10 : Fin 11)=-(intOuter (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨1,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨1,by decide⟩ : Fin shape.m)))) := by
  funext i j
  fin_cases i
  · exact rung1_s_row_0 j
  · exact rung1_s_row_1 j
  · exact rung1_s_row_2 j
  · exact rung1_s_row_3 j
  · exact rung1_s_row_4 j
  · exact rung1_s_row_5 j
  · exact rung1_s_row_6 j
  · exact rung1_s_row_7 j
  · exact rung1_s_row_8 j
  · exact rung1_s_row_9 j
  · exact rung1_s_row_10 j

private theorem rung1_sum_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (0 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j) (by decide +kernel)
private theorem rung1_sum_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (1 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j) (by decide +kernel)
private theorem rung1_sum_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (2 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j) (by decide +kernel)
private theorem rung1_sum_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (3 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j) (by decide +kernel)
private theorem rung1_sum_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (4 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j) (by decide +kernel)
private theorem rung1_sum_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (5 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j) (by decide +kernel)
private theorem rung1_sum_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (6 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j) (by decide +kernel)
private theorem rung1_sum_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (7 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j) (by decide +kernel)
private theorem rung1_sum_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (8 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j) (by decide +kernel)
private theorem rung1_sum_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (9 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j) (by decide +kernel)
private theorem rung1_sum_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (10 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung1_sum : integerChart.phaseMatrix (9 : Fin 11)+integerChart.phaseMatrix (10 : Fin 11)=intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨1,by decide⟩ : Fin shape.m)) (gapPhaseRow shape) := by
  funext i j
  fin_cases i
  · exact rung1_sum_row_0 j
  · exact rung1_sum_row_1 j
  · exact rung1_sum_row_2 j
  · exact rung1_sum_row_3 j
  · exact rung1_sum_row_4 j
  · exact rung1_sum_row_5 j
  · exact rung1_sum_row_6 j
  · exact rung1_sum_row_7 j
  · exact rung1_sum_row_8 j
  · exact rung1_sum_row_9 j
  · exact rung1_sum_row_10 j

private theorem rung2_s_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (0 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 0 j) (by decide +kernel)
private theorem rung2_s_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (1 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 1 j) (by decide +kernel)
private theorem rung2_s_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (2 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 2 j) (by decide +kernel)
private theorem rung2_s_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (3 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 3 j) (by decide +kernel)
private theorem rung2_s_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (4 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 4 j) (by decide +kernel)
private theorem rung2_s_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (5 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 5 j) (by decide +kernel)
private theorem rung2_s_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (6 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 6 j) (by decide +kernel)
private theorem rung2_s_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (7 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 7 j) (by decide +kernel)
private theorem rung2_s_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (8 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 8 j) (by decide +kernel)
private theorem rung2_s_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (9 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 9 j) (by decide +kernel)
private theorem rung2_s_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (8 : Fin 11)) (10 : Fin 11) j=(-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))))) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (8 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide +kernel⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide +kernel⟩ : Fin shape.m))))) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung2_s : integerChart.phaseMatrix (8 : Fin 11)=-(intOuter (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m)))+intOuter (freePhaseRow shape (shape.ySlot (⟨2,by decide⟩ : Fin shape.m))) (freePhaseRow shape (shape.xSlot (⟨2,by decide⟩ : Fin shape.m)))) := by
  funext i j
  fin_cases i
  · exact rung2_s_row_0 j
  · exact rung2_s_row_1 j
  · exact rung2_s_row_2 j
  · exact rung2_s_row_3 j
  · exact rung2_s_row_4 j
  · exact rung2_s_row_5 j
  · exact rung2_s_row_6 j
  · exact rung2_s_row_7 j
  · exact rung2_s_row_8 j
  · exact rung2_s_row_9 j
  · exact rung2_s_row_10 j

private theorem rung2_sum_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (0 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 0 j) (by decide +kernel)
private theorem rung2_sum_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (1 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 1 j) (by decide +kernel)
private theorem rung2_sum_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (2 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 2 j) (by decide +kernel)
private theorem rung2_sum_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (3 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 3 j) (by decide +kernel)
private theorem rung2_sum_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (4 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 4 j) (by decide +kernel)
private theorem rung2_sum_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (5 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 5 j) (by decide +kernel)
private theorem rung2_sum_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (6 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 6 j) (by decide +kernel)
private theorem rung2_sum_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (7 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 7 j) (by decide +kernel)
private theorem rung2_sum_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (8 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 8 j) (by decide +kernel)
private theorem rung2_sum_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (9 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 9 j) (by decide +kernel)
private theorem rung2_sum_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (10 : Fin 11) j=(intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide +kernel⟩ : Fin shape.m)) (gapPhaseRow shape)) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem rung2_sum : integerChart.phaseMatrix (7 : Fin 11)+integerChart.phaseMatrix (8 : Fin 11)=intOuter (gapPhaseRow shape) (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m))+intOuter (pairCorrectionRow shape zeta (⟨2,by decide⟩ : Fin shape.m)) (gapPhaseRow shape) := by
  funext i j
  fin_cases i
  · exact rung2_sum_row_0 j
  · exact rung2_sum_row_1 j
  · exact rung2_sum_row_2 j
  · exact rung2_sum_row_3 j
  · exact rung2_sum_row_4 j
  · exact rung2_sum_row_5 j
  · exact rung2_sum_row_6 j
  · exact rung2_sum_row_7 j
  · exact rung2_sum_row_8 j
  · exact rung2_sum_row_9 j
  · exact rung2_sum_row_10 j

private theorem core_first_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (0 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 0 j) (by decide +kernel)
private theorem core_first_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (1 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 1 j) (by decide +kernel)
private theorem core_first_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (2 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 2 j) (by decide +kernel)
private theorem core_first_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (3 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 3 j) (by decide +kernel)
private theorem core_first_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (4 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 4 j) (by decide +kernel)
private theorem core_first_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (5 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 5 j) (by decide +kernel)
private theorem core_first_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (6 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 6 j) (by decide +kernel)
private theorem core_first_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (7 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 7 j) (by decide +kernel)
private theorem core_first_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (8 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 8 j) (by decide +kernel)
private theorem core_first_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (9 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 9 j) (by decide +kernel)
private theorem core_first_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (4 : Fin 11)) (10 : Fin 11) j=((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l))) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (4 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 0))) i l))) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem core_first : integerChart.phaseMatrix (4 : Fin 11)=(fun i l => (sigma : ℤ)*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1))+intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 1)) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 0))) i l)) := by
  funext i j
  fin_cases i
  · exact core_first_row_0 j
  · exact core_first_row_1 j
  · exact core_first_row_2 j
  · exact core_first_row_3 j
  · exact core_first_row_4 j
  · exact core_first_row_5 j
  · exact core_first_row_6 j
  · exact core_first_row_7 j
  · exact core_first_row_8 j
  · exact core_first_row_9 j
  · exact core_first_row_10 j

private theorem core_second_row_0 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (0 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (0 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 0 j) (by decide +kernel)
private theorem core_second_row_1 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (1 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (1 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 1 j) (by decide +kernel)
private theorem core_second_row_2 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (2 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (2 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 2 j) (by decide +kernel)
private theorem core_second_row_3 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (3 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (3 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 3 j) (by decide +kernel)
private theorem core_second_row_4 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (4 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (4 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 4 j) (by decide +kernel)
private theorem core_second_row_5 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (5 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (5 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 5 j) (by decide +kernel)
private theorem core_second_row_6 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (6 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (6 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 6 j) (by decide +kernel)
private theorem core_second_row_7 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (7 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (7 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 7 j) (by decide +kernel)
private theorem core_second_row_8 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (8 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (8 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 8 j) (by decide +kernel)
private theorem core_second_row_9 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (9 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (9 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 9 j) (by decide +kernel)
private theorem core_second_row_10 : ∀ j : Fin 11,(integerChart.phaseMatrix (5 : Fin 11)) (10 : Fin 11) j=((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l))) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => (integerChart.phaseMatrix (5 : Fin 11)) (10 : Fin 11) j)
    (fun j : Fin 11 => ((fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide +kernel : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) 2))) i l))) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem core_second : integerChart.phaseMatrix (5 : Fin 11)=(fun i l => (sigma : ℤ)*(if coreIsLinear then 1 else (tau : ℤ))*((intOuter (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2)) (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear)+intOuter (coreSecondArgumentRow shape (by decide : VineType.VII.IsBad=false) coreIsLinear) (freePhaseRow shape (shape.uSlot (by decide : VineType.VII.IsBad=false) 2))) i l)) := by
  funext i j
  fin_cases i
  · exact core_second_row_0 j
  · exact core_second_row_1 j
  · exact core_second_row_2 j
  · exact core_second_row_3 j
  · exact core_second_row_4 j
  · exact core_second_row_5 j
  · exact core_second_row_6 j
  · exact core_second_row_7 j
  · exact core_second_row_8 j
  · exact core_second_row_9 j
  · exact core_second_row_10 j

private theorem core_sum_row_0 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (0 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 0 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (0 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 0 j) (by decide +kernel)
private theorem core_sum_row_1 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (1 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 1 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (1 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 1 j) (by decide +kernel)
private theorem core_sum_row_2 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (2 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 2 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (2 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 2 j) (by decide +kernel)
private theorem core_sum_row_3 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (3 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 3 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (3 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 3 j) (by decide +kernel)
private theorem core_sum_row_4 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (4 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 4 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (4 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 4 j) (by decide +kernel)
private theorem core_sum_row_5 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (5 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 5 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (5 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 5 j) (by decide +kernel)
private theorem core_sum_row_6 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (6 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 6 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (6 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 6 j) (by decide +kernel)
private theorem core_sum_row_7 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (7 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 7 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (7 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 7 j) (by decide +kernel)
private theorem core_sum_row_8 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (8 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 8 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (8 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 8 j) (by decide +kernel)
private theorem core_sum_row_9 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (9 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 9 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (9 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 9 j) (by decide +kernel)
private theorem core_sum_row_10 : ∀ j : Fin 11,((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)) (10 : Fin 11) j=(intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 10 j := by
  exact integer_row_eq_of_decide (fun j : Fin 11 => ((∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide +kernel : VineType.VII.IsBad=false) c)).1)) (10 : Fin 11) j)
    (fun j : Fin 11 => (intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide +kernel : VineType.VII.IsBad=false) xi) (gapPhaseRow shape)) 10 j) (by decide +kernel)

/-- Exact finite integer source phase certificate. -/
theorem core_sum : (∑ c : Fin 3,integerChart.phaseMatrix (atomEquiv (shape.uSlot (by decide : VineType.VII.IsBad=false) c)).1)=intOuter (gapPhaseRow shape) (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi)+intOuter (coreCorrectionRow shape (by decide : VineType.VII.IsBad=false) xi) (gapPhaseRow shape) := by
  funext i j
  fin_cases i
  · exact core_sum_row_0 j
  · exact core_sum_row_1 j
  · exact core_sum_row_2 j
  · exact core_sum_row_3 j
  · exact core_sum_row_4 j
  · exact core_sum_row_5 j
  · exact core_sum_row_6 j
  · exact core_sum_row_7 j
  · exact core_sum_row_8 j
  · exact core_sum_row_9 j
  · exact core_sum_row_10 j

/-- The full concrete normalized source certificate, with no input certificate premise. -/
@[expose] noncomputable def certificate : NormalizedVineCertificate .VII where
  shape := shape
  matrix := integerChart
  atom := atomEquiv
  lower := by decide
  joint := jointRow
  reference_row := by decide
  differencePair := differencePair
  difference_rows := by decide
  junction := some ⟨2,by decide⟩
  junction_type := by decide
  rung_bonds := by decide
  ζ := zeta
  ζ_unit := by unfold UnitCoeff; decide
  ζ_bad_nonzero := by intro h; cases h
  coreLinear := coreIsLinear
  coreFirstSign := sigma
  coreSign := tau
  ξ := xi
  ξ_unit := by unfold UnitCoeff; decide
  rung_s_matrix := by
    intro j
    change Fin 3 at j
    fin_cases j
    · exact rung0_s
    · exact rung1_s
    · exact rung2_s
  rung_sum_matrix := by
    intro j
    change Fin 3 at j
    fin_cases j
    · exact rung0_sum
    · exact rung1_sum
    · exact rung2_sum
  core_first_matrix := by intro hn; exact core_first
  core_second_matrix := by intro hn; exact core_second
  core_sum_matrix := by intro hn; exact core_sum

end WaveTurbulence.Vine.Param.Normalized.J0VII009
