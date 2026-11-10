/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedMatrix.J1I000
public import WaveTurbulenceVineParam.VineParamIntegerRowCheck
public import WaveTurbulenceVineParam.VineParamNormalizedBaseShape
public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
import Mathlib.Tactic

/-! # Full finite normalized certificate for vine I, profile 0, joint 1

All source indexing, physical origins and signed phase identities are checked
here as finite integer/combinatorial statements, independently of momenta.
Unused bad-vine core data use the canonical false/unit/zero convention.
-/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J1I000
open Finset VineParamContract

/-- The exact pinned base shape, including II at m=1. -/
@[expose] def shape : Shape .I := normalizedBaseShape .I

/-- Actual included atoms in reference/x/y/core contract order. -/
@[expose] def atomVector : Fin 1 → Fin 2 := fun _i => 1

/-- Every actual included atom differs from the excluded joint. -/
theorem atomVector_ne : ∀ i,atomVector i ≠ (0 : Fin 2) := by decide +kernel

/-- Explicit actual included-atom bijection. -/
@[expose] noncomputable def atomEquiv : Fin 1 ≃ {v : Fin 2 // v ≠ (0 : Fin 2)} :=
  Equiv.ofBijective (fun i => ⟨atomVector i,atomVector_ne i⟩) (by decide)

/-- The actual physical two-occurrence joint row. -/
@[expose] noncomputable def jointRow : DirectedJointRow integerChart.ends integerChart.b where
  outgoing := 1
  incoming := 0
  distinct := by decide
  outgoing_at := by decide
  incoming_at := by decide
  row := by decide

/-- There are no nonreference coordinates in vine I. -/
@[expose] def differencePair (i : {i : Fin shape.n // i ≠ shape.x0}) : Fin (2*shape.n)×Fin (2*shape.n) := by
  have hv : i.1.1<1 := i.1.2
  have hn : i.1.1 ≠ 0 := by intro h; apply i.2; exact Fin.ext h
  exact False.elim (by omega)

/-- Actual paired phase correction coefficients. -/
@[expose] def zeta : Fin shape.m → Fin 3 → ℤ := Fin.elim0

/-- Actual normal-core correction coefficients (zero for bad vines). -/
@[expose] def xi : Fin 4 → ℤ := fun i => if i.1 < 2 then (if i.1 < 1 then (0) else (0)) else (if i.1 < 3 then (0) else (0))

/-- Common actual core phase sign. -/
@[expose] def sigma : ℤˣ := 1

/-- Relative nonlinear sign in the owner-approved F79 convention. -/
@[expose] def tau : ℤˣ := 1

/-- Which of the two actual source core alternatives occurs. -/
@[expose] def coreIsLinear : Bool := false

/-- The full concrete normalized source certificate, with no input certificate premise. -/
@[expose] noncomputable def certificate : NormalizedVineCertificate .I where
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
    exact Fin.elim0 j
  rung_sum_matrix := by
    intro j
    exact Fin.elim0 j
  core_first_matrix := by intro h; cases h
  core_second_matrix := by intro h; cases h
  core_sum_matrix := by intro h; cases h

end WaveTurbulence.Vine.Param.Normalized.J1I000
