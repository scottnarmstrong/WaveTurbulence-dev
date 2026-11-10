/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.InsertMiniTree
public import WaveTurbulence.Foundations.RegStruct.PairNaturality
public import WaveTurbulence.Foundations.RegStruct.RawAddressUpdate

/-! # Literal address transport for operation B at either original root -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The one-pair chain is precisely the source mini-tree context. -/
theorem miniChain_plug (m : MiniTreeCode) (ζ : ℤˣ) (s : TTree) :
    (miniChain m).plug ζ s = miniTreeContext m s := by
  simp [miniChain,RegChain.plug,RegCpl.trees,node3,treeOfSign,miniTreeContext]

/-- The one-pair chain's lone path is the mini-tree's two-slot path. -/
theorem miniChain_lonePath (m : MiniTreeCode) : (miniChain m).lonePath = [m.c,m.lone] := rfl

/-- The two new oriented pairs are exactly the source red/green mini-tree pairs. -/
theorem miniChain_pairsAt (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin 2 × Path) :
    (miniChain m).pairsAt ζ a =
      [RawCpl.orient (addrExt a [m.red.1]) (slotSign ζ m.red.1) (addrExt a [m.c,m.red.2]),
       RawCpl.orient (addrExt a [m.green.1]) (slotSign ζ m.green.1) (addrExt a [m.c,m.green.2])] := by
  by_cases hr : slotSign ζ m.red.1 = 1 <;>
    by_cases hg : slotSign ζ m.green.1 = 1 <;>
    simp [miniChain,RegChain.pairsAt,RegCpl.pairsAt,RegChain.lonePath,RawCpl.orient,hr,hg]

/-- Root signs of a source-oriented couple. -/
theorem nodeSign_root_zero : nodeSign ![1,-1] ((0 : Fin 2),[]) = 1 := by
  simp [nodeSign,pathSign]

theorem nodeSign_root_one : nodeSign ![1,-1] ((1 : Fin 2),[]) = -1 := by
  simp [nodeSign,pathSign]

end WaveTurbulence.Reg
