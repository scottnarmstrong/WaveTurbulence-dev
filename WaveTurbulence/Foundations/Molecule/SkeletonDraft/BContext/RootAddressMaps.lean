/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.RegStruct.InsertMiniTree
public import WaveTurbulence.Foundations.RegStruct.PairNaturality
public import WaveTurbulence.Foundations.RegStruct.RawAddressUpdate


/-! # Literal address transport for operation B at either original root -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

theorem miniChain_pairsAt (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin w × Path) :
    (miniChain m).pairsAt ζ a =
      [WaveTurbulence.Reg.Skeleton.orient (addrExt a [m.red.1]) (slotSign ζ m.red.1) (addrExt a [m.c,m.red.2]),
       WaveTurbulence.Reg.Skeleton.orient (addrExt a [m.green.1]) (slotSign ζ m.green.1) (addrExt a [m.c,m.green.2])] := by
  by_cases hr : slotSign ζ m.red.1 = 1 <;>
    by_cases hg : slotSign ζ m.green.1 = 1 <;>
    simp [miniChain,RegChain.pairsAt,RegCpl.pairsAt,RegChain.lonePath,WaveTurbulence.Reg.Skeleton.orient,hr,hg]


end WaveTurbulence.Reg.Skeleton.BContext
