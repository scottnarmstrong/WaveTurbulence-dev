/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainBranches
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality
public import WaveTurbulence.Foundations.RegStruct.PairRelations
public import WaveTurbulence.Foundations.RegStruct.TreeDecodingAuxiliary

/-! # Actual node and pair transport for native regular paired-tree replacements -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem chain_nodes_subset_plug (X : RegChain) (ζ : ℤˣ) (h : TTree) :
    (X.plug ζ .leaf).nodes ⊆ (X.plug ζ h).nodes := by
  intro q hq
  have hm : addrExt ((0 : Fin 1),[]) q ∈ nodeAddresses (X.plug ζ .leaf) (0,[]) :=
    Finset.mem_image.mpr ⟨q,hq,rfl⟩
  rw [chain_nodeAddresses,nodeAddresses_leaf] at hm
  have hn : addrExt ((0 : Fin 1),[]) q ∈ nodeAddresses (X.plug ζ h) (0,[]) := by
    rw [chain_nodeAddresses]
    rcases Finset.mem_union.mp hm with hc | hc
    · exact Finset.mem_union_left _ hc
    · have he := Finset.mem_singleton.mp hc
      rw [he]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[],nil_mem_nodes h,by
        simp only [addrExt,List.append_nil]⟩)
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hn
  have heq : r = q := by
    have hp := congrArg Prod.snd he
    exact hp
  exact heq ▸ hr

noncomputable def chainContextNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) : GNode (D.forest hS) :=
  ⟨addrExt (inflatedPosition S D.tree b.toNode) a.1.2,by
    have hs := (D.forest_subtree_position hS b.toNode).trans
      (congrArg some (D.inflateNode_branch hS b))
    exact (Comb.subtree_nodes_iff hs a.1.2).mp (chain_nodes_subset_plug _ _ _ a.2)⟩

theorem chainContextNode_child {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree)
    (a : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) (i : Fin 3) :
    chainContextNode D hS b (a.child i) =
      (chainContextBranch D hS b ⟨a.1.2,a.2⟩).child i := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_assoc _ _ _).symm

theorem layer_eq_of_sourcePair {w : ℕ} (LG : LayeredGarden w)
    (x y : GNode LG.garden.tree) (h : (x.1,y.1) ∈ sourcePairs LG.garden) :
    LG.layer x = LG.layer y := by
  obtain ⟨ℓ,q,hℓ,hq,hpair⟩ := sourcePairs_actual_endpoints LG.garden _ h
  have hx : x = ℓ.toNode := Subtype.ext hℓ.symm
  have hy : y = q.toNode := Subtype.ext hq.symm
  rw [hx,hy,← hpair]
  exact LG.isLayering.2 ℓ

end WaveTurbulence.RegRed
