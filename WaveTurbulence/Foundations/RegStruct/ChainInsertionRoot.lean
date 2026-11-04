/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationBRoots
public import WaveTurbulence.Foundations.RegStruct.NodeSeparation
public import WaveTurbulence.Foundations.RegStruct.ChainPairLocations

/-! # Operation B at a represented chain root

This is a local source identity at an arbitrary global address and root sign,
not just at one of the original two couple roots.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The insertion root moves to the newly created lone slot. -/
theorem relocate_self (a : Fin 2 × Path) (c l : Fin 3) :
    RawCpl.relocate a c l a = addrExt a [c,l] := by
  simp [RawCpl.relocate,addrExt]

/-- Exact pair-list fidelity when B is inserted before a nonempty chain. -/
theorem insertMiniChain_root_pairs (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin 2 × Path) :
    ((insertMiniChain (.pair k r g i s) ζ a a m).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map
        (fun p => (RawCpl.relocate a m.c m.lone p.1,RawCpl.relocate a m.c m.lone p.2)) ++
        (miniChain m).pairsAt ζ a) := by
  rw [insertMiniChain_at_root]
  change ((appendChain (miniChain m) (.pair k r g i s)).pairsAt ζ a).Perm _
  rw [appendChain_pairsAt,miniChain_lonePath]
  have hlocal : RespectsAt (RawCpl.relocate a m.c m.lone) a :=
    relocate_respects_desc a a m.c m.lone ⟨rfl,List.prefix_refl _⟩
  have hm := chain_pairsAt_map_local (.pair k r g i s) (RawCpl.relocate a m.c m.lone) a hlocal ζ
  rw [relocate_self] at hm
  rw [hm]
  exact List.perm_append_comm

/-- The actual terminal hole is relocated along with the old chain. -/
theorem insertMiniChain_root_lonePath (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin 2 × Path) :
    addrExt a (insertMiniChain (.pair k r g i s) ζ a a m).lonePath =
      RawCpl.relocate a m.c m.lone (addrExt a (RegChain.pair k r g i s).lonePath) := by
  rw [insertMiniChain_at_root]
  change addrExt a (appendChain (miniChain m) (.pair k r g i s)).lonePath = _
  rw [appendChain_lonePath,miniChain_lonePath]
  have hlocal : RespectsAt (RawCpl.relocate a m.c m.lone) a :=
    relocate_respects_desc a a m.c m.lone ⟨rfl,List.prefix_refl _⟩
  rw [hlocal _,relocate_self,addrExt_append]

end WaveTurbulence.Reg
