/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ExternalSpineSegments

/-! # Exact inner/lower/rest subtree frames of a chain pair -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The source's lower branching node, including its three actual subtrees. -/
def chainLowerTree (k : MiniTreeCode) (r g : RegCpl) (s : RegChain) (ζ : ℤˣ) (h : TTree) : TTree :=
  node3 fun j => if j = k.lone then s.plug (slotSign (slotSign ζ k.c) j) h
    else if j = k.red.2 then treeOfSign r.trees (slotSign (slotSign ζ k.c) j)
    else treeOfSign g.trees (slotSign (slotSign ζ k.c) j)

/-- Extraction of a selected child of a three-child node. -/
theorem node3_subtree_singleton (f : Fin 3 → TTree) (j : Fin 3) :
    Comb.subtree (node3 f) [j] = some (f j) := by
  fin_cases j <;> simp [node3,Comb.subtree]

/-- The first continuation child is the inner chain filled by the actual lower node. -/
theorem chain_inner_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) [k.c] =
      some (i.plug (slotSign ζ k.c) (chainLowerTree k r g s ζ h)) := by
  rw [RegChain.plug,node3_subtree_singleton]
  simp only [ite_true]
  rfl

/-- The hole of the inner chain contains precisely the lower branching node. -/
theorem chain_second_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) ([k.c] ++ i.lonePath) =
      some (chainLowerTree k r g s ζ h) := by
  rw [Comb.subtree_append,chain_inner_subtree]
  exact plug_subtree_lonePath i _ _

/-- The lower continuation child is exactly the rest chain with the original filling. -/
theorem chain_rest_subtree (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree) :
    Comb.subtree ((RegChain.pair k r g i s).plug ζ h) ([k.c] ++ i.lonePath ++ [k.lone]) =
      some (s.plug (slotSign (slotSign ζ k.c) k.lone) h) := by
  rw [Comb.subtree_append,chain_second_subtree]
  change Comb.subtree (chainLowerTree k r g s ζ h) [k.lone] = _
  rw [chainLowerTree,node3_subtree_singleton]
  simp only [ite_true]

/-- Restate the whole hole as the terminal address of the lower continuation. -/
theorem chain_hole_as_rest {w : ℕ} (a : Fin w × Path) (k : MiniTreeCode)
    (r g : RegCpl) (i s : RegChain) :
    addrExt a (RegChain.pair k r g i s).lonePath = addrExt (backRoot a k i k.lone) s.lonePath := by
  simp only [RegChain.lonePath,backRoot,addrExt_append,List.append_assoc]

end WaveTurbulence.Reg
