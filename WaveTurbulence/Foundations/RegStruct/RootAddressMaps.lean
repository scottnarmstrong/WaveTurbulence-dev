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

/-- Prefix all addresses in one original tree, leaving the other trees unchanged. -/
def prefixTree {w : ℕ} (j : Fin w) (p : Path) (a : Fin w × Path) : Fin w × Path :=
  if a.1 = j then (a.1,p ++ a.2) else a

/-- Whole-tree prefix transport respects all path extensions. -/
theorem prefixTree_respects {w : ℕ} (j : Fin w) (p : Path) (a : Fin w × Path) (q : Path) :
    prefixTree j p (addrExt a q) = addrExt (prefixTree j p a) q := by
  obtain ⟨k,r⟩ := a
  by_cases h : k = j <;> simp [prefixTree,addrExt,h,List.append_assoc]

@[simp] theorem prefixTree_root_self {w : ℕ} (j : Fin w) (p : Path) :
    prefixTree j p (j,[]) = (j,p) := by simp [prefixTree]

theorem prefixTree_root_other {w : ℕ} (j k : Fin w) (h : k ≠ j) (p : Path) :
    prefixTree j p (k,[]) = (k,[]) := by simp [prefixTree,h]

/-- Source relocation at an original root is exactly whole-tree prefix insertion. -/
theorem relocate_root (j : Fin 2) (c l : Fin 3) (z : Fin 2 × Path) :
    RawCpl.relocate (j,[]) c l z = prefixTree j [c,l] z := by
  simp [RawCpl.relocate,prefixTree]

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

/-- The raw B-step at a root shifts every old pair and appends the two mini-tree pairs. -/
theorem raw_opB_root_pairs (R : RawCpl) (j : Fin 2) (m : MiniTreeCode) :
    (R.opB (j,[]) m).2 =
      R.2.map (fun p => (prefixTree j [m.c,m.lone] p.1,prefixTree j [m.c,m.lone] p.2)) ++
      (miniChain m).pairsAt (nodeSign ![1,-1] (j,[])) (j,[]) := by
  simp only [RawCpl.opB,relocate_root,miniChain_pairsAt]

/-- Root signs of a source-oriented couple. -/
theorem nodeSign_root_zero : nodeSign ![1,-1] ((0 : Fin 2),[]) = 1 := by
  simp [nodeSign,pathSign]

theorem nodeSign_root_one : nodeSign ![1,-1] ((1 : Fin 2),[]) = -1 := by
  simp [nodeSign,pathSign]

end WaveTurbulence.Reg
