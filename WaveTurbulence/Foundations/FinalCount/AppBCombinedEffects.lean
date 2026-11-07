/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCombinedRemoval
public import WaveTurbulence.Foundations.FinalCount.AppBEraseUnionIso
import Mathlib.Tactic

/-! # Exact atoms and components of a combined literal deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P Q : AppbPattern}

theorem removedAtoms_card (r : AppbRealization M P) : r.removedAtoms.card = P.removed.card :=
  card_image_of_injOn (r.vertex_injective.mono (by intro a ha; exact mem_union_left _ ha))

theorem combinedRemovedAtoms_card (r : AppbRealization M P) (s : AppbRealization r.post Q) :
    (r.combinedRemovedAtoms s).card = P.removed.card+Q.removed.card := by
  have hd : Disjoint r.removedAtoms s.removedAtoms := by
    apply disjoint_left.mpr
    intro v hv hs
    exact (mem_sdiff.mp (s.removedAtoms_subset hs)).2 hv
  change (r.removedAtoms ∪ s.removedAtoms).card = _
  rw [card_union_of_disjoint hd,r.removedAtoms_card,s.removedAtoms_card]

theorem combinedRemoval_removed_card (r : AppbRealization M P) (s : AppbRealization r.post Q) (v0 : M.atoms) :
    (r.combinedRemoval s v0).removedAtoms.card = P.removed.card+Q.removed.card := by
  rw [r.combinedRemoval_removed,r.combinedRemovedAtoms_card]

theorem combinedPattern_removed_card (r : AppbRealization M P) (s : AppbRealization r.post Q) (v0 : M.atoms) :
    (r.combinedPattern s).removed.card = P.removed.card+Q.removed.card :=
  (r.combinedRemoval s v0).removedAtoms_card.symm.trans (r.combinedRemoval_removed_card s v0)

theorem combinedRemoval_components (r : AppbRealization M P) (s : AppbRealization r.post Q) (v0 : M.atoms) :
    (r.combinedRemoval s v0).post.numComponents = s.post.numComponents := by
  have hh := (appbEraseAtomsUnionIso M r.removedAtoms s.removedAtoms).appb_numComponents_eq
  change (Degen.eraseAtoms M (r.combinedRemoval s v0).removedAtoms).numComponents = s.post.numComponents
  rw [r.combinedRemoval_removed]
  exact hh.symm

end AppbRealization
end WaveTurbulence.Mole
