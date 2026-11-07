/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalize
public import WaveTurbulenceVineParam.VineParamGrouped

/-! # `normalizeChart` preserves the cohmol groups of a chart (R22 (3))

`chartAtomGroups` (rung pairs and core triple, as atom sets) is invariant under a permutation of the rungs.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence VineParamContract Finset WaveTurbulence.Vine.Param

variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V} {X : VineType}

theorem chartAtomGroups_reindex (C : FullVineChart M X S a b) (σ : Equiv.Perm (Fin C.indexing.shape.m)) :
    chartAtomGroups (FullVineChart.reindex C σ) = chartAtomGroups C := by
  classical
  unfold chartAtomGroups shapeGroupSet
  show (univ.image fun j : Fin C.indexing.shape.m =>
        ({(C.indexing.atom (slotPerm C.indexing.shape σ (C.indexing.shape.xSlot j))).1,
          (C.indexing.atom (slotPerm C.indexing.shape σ (C.indexing.shape.ySlot j))).1} : Finset V)) ∪
      (if hn : X.IsBad = false then
        {({(C.indexing.atom (slotPerm C.indexing.shape σ (C.indexing.shape.uSlot hn 0))).1,
           (C.indexing.atom (slotPerm C.indexing.shape σ (C.indexing.shape.uSlot hn 1))).1,
           (C.indexing.atom (slotPerm C.indexing.shape σ (C.indexing.shape.uSlot hn 2))).1} : Finset V)}
        else (∅ : Finset (Finset V))) = _
  simp only [slotPerm_xSlot, slotPerm_ySlot, slotPerm_uSlot]
  congr 1
  ext g
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨σ j, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨σ.symm j, by simp⟩

theorem chartAtomGroups_normalizeChart (C : FullVineChart M X S a b) :
    chartAtomGroups (normalizeChart C) = chartAtomGroups C := by
  unfold normalizeChart
  split_ifs
  · exact chartAtomGroups_reindex _ _
  · rfl

end WaveTurbulence.VineEstS2
