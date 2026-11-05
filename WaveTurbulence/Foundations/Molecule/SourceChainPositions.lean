/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainSpineInsertion
public import WaveTurbulence.Foundations.Molecule.DominantChains

/-! # Actual branching-or-lone source positions of saturated chain insertions -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The source tree's side in its auxiliary positive/negative couple. -/
def chainSide (ζ : ℤˣ) : Fin 2 := if ζ = 1 then 0 else 1

/-- The chosen side carries exactly the requested incoming root sign. -/
theorem nodeSign_chainSide (ζ : ℤˣ) : nodeSign ![1,-1] (chainSide ζ,[]) = ζ := by
  by_cases hζ : ζ = 1
  · subst ζ
    exact nodeSign_root_zero
  · have hm : ζ = -1 := (Int.units_eq_one_or _).resolve_left hζ
    subst ζ
    exact nodeSign_root_one

/-- The auxiliary couple's chosen tree is literally the decoded chain tree. -/
theorem treeAuxCode_own_tree (X : RegChain) (ζ : ℤˣ) :
    coupleForest (treeAuxCode X ζ) (chainSide ζ) = X.plug ζ .leaf := by
  by_cases hζ : ζ = 1
  · subst ζ
    change (treeAuxCode X 1).trees.1 = _
    rw [treeAuxCode_trees,ite_eq_left rfl]
  · have hm : ζ = -1 := (Int.units_eq_one_or _).resolve_left hζ
    subst ζ
    change (treeAuxCode X (-1)).trees.2 = _
    rw [treeAuxCode_trees,ite_eq_right (by decide)]

/-- Every actual node in the tree is represented by the chain or by its one lone slot. -/
theorem chain_position_of_tree_node (X : RegChain) (ζ : ℤˣ) (s : Fin 2) (p : Path)
    (hp : p ∈ (X.plug ζ .leaf).nodes) :
    (s,p) ∈ chainNodes X ζ (s,[]) ∨ (s,p) = addrExt (s,[]) X.lonePath := by
  have hm : (s,p) ∈ nodeAddresses (X.plug ζ .leaf) (s,[]) := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  rw [chain_nodeAddresses,nodeAddresses_leaf,Finset.mem_union,Finset.mem_singleton] at hm
  exact hm

/-- Branching nodes of a bare chain, and its lone leaf, are exactly permitted source spine positions. -/
theorem bareChain_permitted_spine (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) (s : Fin 2) (p : Path)
    (hp : p ∈ (X.plug ζ .leaf).branching ∨ p = X.lonePath) : Below (s,p) (s,X.lonePath) := by
  rcases hp with hp | rfl
  · rw [bareChain_plug_spine X hX,spineContext_branching] at hp
    exact ⟨rfl,(mem_spinePrefixes hp).1⟩
  · exact ⟨rfl,List.prefix_refl _⟩

/-- An actual tree node on the root-to-lone path is branching or the lone leaf. -/
theorem chain_node_on_spine_permitted (X : RegChain) (ζ : ℤˣ) (p : Path)
    (hp : p ∈ (X.plug ζ .leaf).nodes) (hpath : p <+: X.lonePath) :
    p ∈ (X.plug ζ .leaf).branching ∨ p = X.lonePath := by
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp hp with hleaf | hbranch
  · exact Or.inr (leaf_prefix_node_eq hleaf (TTree.leaves_subset_nodes _ (chain_lone_mem_leaves X ζ)) hpath)
  · exact Or.inl hbranch

/-- The constructive bare-chain pruning step necessarily inserts on the source lone-leaf spine. -/
theorem bareChain_prune_above_lone (X Y : RegChain) (hX : BareChain X) (hY : BareChain Y)
    (ζ : ℤˣ) (target : Fin 2 × Path) (m : MiniTreeCode) (hsize : Y.size+2 = X.size)
    (ht : target ∈ chainNodes Y ζ (chainSide ζ,[]) ∨ target = addrExt (chainSide ζ,[]) Y.lonePath)
    (he : insertChainMini Y ζ (chainSide ζ,[]) target m = X) :
    Below target (chainSide ζ,Y.lonePath) := by
  by_contra hn
  have hf := insertChainMini_pairs Y ![1,-1] ζ (chainSide ζ,[]) target m (nodeSign_chainSide ζ) ht
  rw [he] at hf
  have hfixed := relocate_eq_of_not_below target m.c m.lone (chainSide ζ,Y.lonePath) hn
  have heAddr : (chainSide ζ,X.lonePath) = (chainSide ζ,Y.lonePath) := hf.2.trans hfixed
  have hpath := congrArg (fun z : Fin 2 × Path => z.2) heAddr
  have hlength := congrArg List.length hpath
  change X.lonePath.length = Y.lonePath.length at hlength
  have hx := bareChain_lonePath_length X hX
  have hy := bareChain_lonePath_length Y hY
  have hxs := bareChain_size X hX
  have hys := bareChain_size Y hY
  omega

/-- DH21 Definition 4.6's actual B-only construction in the auxiliary couple.
The chosen node is branching in the chain tree or is the specified lone leaf;
its actual node membership is retained as typing data. -/
inductive RawChainHistory (ζ : ℤˣ) : RawCpl → Path → Prop
  | triv : RawChainHistory ζ ((.leaf,.leaf),[((0,[]),(1,[]))]) []
  | opB {R : RawCpl} {lp : Path} {a : Fin 2 × Path} (m : MiniTreeCode) :
      RawChainHistory ζ R lp → a.1 = chainSide ζ →
      (a.2 ∈ (R.tree (chainSide ζ)).branching ∨ a.2 = lp) →
      a.2 ∈ (R.tree a.1).nodes →
      RawChainHistory ζ (R.opB a m) (RawCpl.relocate a m.c m.lone (chainSide ζ,lp)).2

/-- Every permitted actual chain history is an actual source regular-couple history. -/
theorem RawChainHistory.rawRegular {ζ : ℤˣ} {R : RawCpl} {lp : Path} (h : RawChainHistory ζ R lp) : RawRegular R := by
  induction h with
  | triv => exact .triv
  | opB m _ _ _ hnode ih => exact .opB m ih hnode

end WaveTurbulence.Reg
