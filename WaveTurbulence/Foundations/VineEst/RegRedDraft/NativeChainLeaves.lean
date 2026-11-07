/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainNodes
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionLeafCoverage

/-! # Actual nonlone leaves of regular paired-tree contexts survive arbitrary filling -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem chain_leaf_mem_plug_of_ne_lone (X : RegChain) (ζ : ℤˣ) (h : TTree) (q : Path)
    (hq : q ∈ (X.plug ζ .leaf).leaves) (hne : q ≠ X.lonePath) : q ∈ (X.plug ζ h).leaves := by
  have hm : addrExt ((0 : Fin 1),[]) q ∈ leafAddresses (X.plug ζ .leaf) (0,[]) :=
    Finset.mem_image.mpr ⟨q,hq,rfl⟩
  rw [chain_leafAddresses,leafAddresses_leaf] at hm
  have hp : addrExt ((0 : Fin 1),[]) q ∈ pairEndpoints (X.pairsAt ζ (0,[])) := by
    rcases Finset.mem_union.mp hm with hc | hc
    · exact hc
    · exact (hne (congrArg Prod.snd (Finset.mem_singleton.mp hc))).elim
  have hn : addrExt ((0 : Fin 1),[]) q ∈ leafAddresses (X.plug ζ h) (0,[]) := by
    rw [chain_leafAddresses]
    exact Finset.mem_union_left _ hp
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hn
  have heq : r = q := congrArg Prod.snd he
  exact heq ▸ hr

abbrev ChainInternalLeaf {w : ℕ} {S : Garden w} (D : ReconstructionData S) (b : GBranch S.tree) :=
  {ℓ : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree // ℓ.1.2 ≠ (D.tree b).lonePath}

noncomputable def chainContextLeaf {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (ℓ : ChainInternalLeaf D b) : GLeaf (D.forest hS) :=
  ⟨addrExt (inflatedPosition S D.tree b.toNode) ℓ.1.1.2,by
    have hs := (D.forest_subtree_position hS b.toNode).trans
      (congrArg some (D.inflateNode_branch hS b))
    exact (Comb.subtree_leaves_iff hs ℓ.1.1.2).mp (chain_leaf_mem_plug_of_ne_lone _ _ _ _ ℓ.1.2 ℓ.2)⟩

theorem chainContextLeaf_toNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (ℓ : ChainInternalLeaf D b) :
    (chainContextLeaf D hS b ℓ).toNode = chainContextNode D hS b ℓ.1.toNode := Subtype.ext rfl

end WaveTurbulence.RegRed
