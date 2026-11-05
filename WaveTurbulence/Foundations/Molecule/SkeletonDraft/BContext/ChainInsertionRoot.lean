/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.RegStruct.OperationBRoots
public import WaveTurbulence.Foundations.RegStruct.NodeSeparation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainPairLocations


/-! # Operation B at a represented chain root

This is a local source identity at an arbitrary global address and root sign,
not just at one of the original two couple roots.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- The insertion root moves to the newly created lone slot. -/
theorem relocate_self (a : Fin w × Path) (c l : Fin 3) :
    WaveTurbulence.Reg.Skeleton.relocate a c l a = addrExt a [c,l] := by
  simp [WaveTurbulence.Reg.Skeleton.relocate,addrExt]

/-- Exact pair-list fidelity when B is inserted before a nonempty chain. -/
theorem insertMiniChain_root_pairs (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ((insertMiniChain (.pair k r g i s) ζ a a m).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map
        (fun p => (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone p.2)) ++
        (miniChain m).pairsAt ζ a) := by
  rw [insertMiniChain_at_root]
  change ((appendChain (miniChain m) (.pair k r g i s)).pairsAt ζ a).Perm _
  rw [appendChain_pairsAt,miniChain_lonePath]
  have hlocal : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) a :=
    relocate_respects_desc a a m.c m.lone ⟨rfl,List.prefix_refl _⟩
  have hm := chain_pairsAt_map_local (.pair k r g i s) (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) a hlocal ζ
  rw [relocate_self] at hm
  rw [hm]
  exact List.perm_append_comm

/-- The actual terminal hole is relocated along with the old chain. -/
theorem insertMiniChain_root_lonePath (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    addrExt a (insertMiniChain (.pair k r g i s) ζ a a m).lonePath =
      WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone (addrExt a (RegChain.pair k r g i s).lonePath) := by
  rw [insertMiniChain_at_root]
  change addrExt a (appendChain (miniChain m) (.pair k r g i s)).lonePath = _
  rw [appendChain_lonePath,miniChain_lonePath]
  have hlocal : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) a :=
    relocate_respects_desc a a m.c m.lone ⟨rfl,List.prefix_refl _⟩
  rw [hlocal _,relocate_self,addrExt_append]

end WaveTurbulence.Reg.Skeleton.BContext
