/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.CoupleInsertionRootsLocal
public import WaveTurbulence.Foundations.RegStruct.InsertionOutside


/-! # Stable code blocks outside an operation-B insertion frame -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

theorem insertMiniCouple_of_incomparable (Q : RegCpl) (a b target : Fin w × Path)
    (m : MiniTreeCode) (ha : IncompAddr target a) (hb : IncompAddr target b) :
    insertMiniCouple Q a b target m = Q :=
  insertMiniCouple_outside Q a b target m
    (not_mem_coupleNodes_of_below Q ⟨rfl,List.prefix_refl _⟩ ha hb)

/-- All pairs in a separated couple are fixed by the literal source relocation. -/
theorem relocate_couple_pairs_fixed (Q : RegCpl) (a b target : Fin w × Path)
    (m : MiniTreeCode) (ha : IncompAddr target a) (hb : IncompAddr target b) :
    (Q.pairsAt a b).map (fun p =>
      (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) = Q.pairsAt a b := by
  have hlocalA := relocate_respects_incomparable target a m.c m.lone ha.1 ha.2
  have hlocalB := relocate_respects_incomparable target b m.c m.lone hb.1 hb.2
  have he := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone) a b hlocalA hlocalB
  rw [relocate_eq_of_not_below _ _ _ _ ha.1,relocate_eq_of_not_below _ _ _ _ hb.1] at he
  exact he.symm

/-- A separated chain is not visited by code operation B. -/
theorem insertMiniChain_of_incomparable (X : RegChain) (ζ : ℤˣ) (a target : Fin w × Path)
    (m : MiniTreeCode) (ha : IncompAddr target a) : insertMiniChain X ζ a target m = X :=
  insertMiniChain_outside X ζ a target m
    (not_mem_chainNodes_of_below X ζ ⟨rfl,List.prefix_refl _⟩ ha)

/-- The entire pair block of a separated chain remains fixed. -/
theorem relocate_chain_pairs_fixed (X : RegChain) (ζ : ℤˣ) (a target : Fin w × Path)
    (m : MiniTreeCode) (ha : IncompAddr target a) :
    (X.pairsAt ζ a).map (fun p =>
      (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) = X.pairsAt ζ a := by
  have hlocal := relocate_respects_incomparable target a m.c m.lone ha.1 ha.2
  have he := chain_pairsAt_map_local X (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone) a hlocal ζ
  rw [relocate_eq_of_not_below _ _ _ _ ha.1] at he
  exact he.symm

end WaveTurbulence.Reg.Skeleton.BContext
