/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamReflectedIndexing
public import WaveTurbulenceVineParam.VineParamPhysicalGraphChart
public import WaveTurbulenceVineParam.VineParamPhysicalGraphIso
import Mathlib.Tactic

/-! # The chart groups of a full vine chart (TARGET cohmol, chart side)

The groups of a chart are the rung pairs `{xSlot j, ySlot j}` and, for the normal types, the
core triple `{uSlot 0, uSlot 1, uSlot 2}`. Here they are recorded as a finset of finsets of
natural-number labels, so that they can be compared with the template groups
`(X.expand k).groups` after pushing the atoms through a labelling.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

/-- Template groups as a finset of finsets of labels. -/
@[expose] def listGroupSet (gs : List (List ℕ)) : Finset (Finset ℕ) :=
  (gs.map List.toFinset).toFinset

/-- The groups of a chart shape, read through a labelling of the slots. -/
@[expose] def shapeGroupSet {α : Type*} [DecidableEq α] {X : VineType} (A : Shape X)
    (ℓ : Fin A.n → α) : Finset (Finset α) :=
  (univ.image fun j : Fin A.m => ({ℓ (A.xSlot j), ℓ (A.ySlot j)} : Finset α)) ∪
    (if hn : X.IsBad = false then
      {({ℓ (A.uSlot hn 0), ℓ (A.uSlot hn 1), ℓ (A.uSlot hn 2)} : Finset α)}
      else (∅ : Finset (Finset α)))

/-- The groups of a chart indexing, read through a labelling of the atoms. -/
@[expose] def indexingGroupSet {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {X : VineType} {S : Finset V}
    {a b : V} (I : Indexing M X S a b) (ℓ : V → ℕ) : Finset (Finset ℕ) :=
  shapeGroupSet I.shape (fun i => ℓ (I.atom i).1)

theorem shapeGroupSet_map {α β : Type*} [DecidableEq α] [DecidableEq β] {X : VineType}
    (A : Shape X) (ℓ : Fin A.n → α) (ψ : α → β) :
    shapeGroupSet A (fun i => ψ (ℓ i)) = (shapeGroupSet A ℓ).image (Finset.image ψ) := by
  classical
  unfold shapeGroupSet
  rw [Finset.image_union, Finset.image_image]
  congr 1
  · apply Finset.image_congr
    intro j _
    simp [Finset.image_insert, Finset.image_singleton]
  · by_cases hn : X.IsBad = false
    · simp [hn, Finset.image_insert, Finset.image_singleton]
    · simp [hn]

end WaveTurbulence.Vine.Param
