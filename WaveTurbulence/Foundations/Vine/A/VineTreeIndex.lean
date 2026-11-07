/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
public import WaveTurbulence.Foundations.Vine.A.VineCoupleIndex
import Mathlib.Tactic

/-!
# S2 REPRESENTS: links of a native tree inside the reconstruction
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed
  WaveTurbulence.LFTwist WaveTurbulence.Links

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The address map of the embedding of a native tree. -/
def chainAddr (b : GBranch S.tree) (x : Fin 1 × TTree.Path) : Fin w × TTree.Path :=
  addrExt (inflatedPosition S D.tree b.toNode) x.2

theorem chainAddr_respects (b : GBranch S.tree) : RespectsAt (chainAddr D b) ((0 : Fin 1), []) := by
  intro q
  simp [chainAddr, addrExt]

theorem chainLinksAt_eq_map (b : GBranch S.tree) :
    (D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) =
      ((D.tree b).treeLinks (nodeSign S.sig b.1)).map
        (fun l => (chainAddr D b l.1, chainAddr D b l.2)) := by
  have h0 : chainAddr D b ((0 : Fin 1), []) = inflatedPosition S D.tree b.toNode := by
    simp [chainAddr, addrExt]
  have := chain_linksAt_map_local (D.tree b) (chainAddr D b) ((0 : Fin 1), []) (chainAddr_respects D b)
    (nodeSign S.sig b.1)
  rw [h0] at this
  exact this

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem chain_layerAt (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    layerAt (layeredReconstruction D hS layer hLayer) (chainAddr D b a.1) =
      (nativeChainLayered D hS layer hLayer b).layer a :=
  layerAt_node (layeredReconstruction D hS layer hLayer) (chainContextNode D hS b a)

theorem chain_layerAt_of_mem (b : GBranch S.tree) (x : Fin 1 × TTree.Path)
    (hx : x.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree x.1).nodes) :
    layerAt (layeredReconstruction D hS layer hLayer) (chainAddr D b x) =
      layerAt (nativeChainLayered D hS layer hLayer b) x :=
  (chain_layerAt D hS layer hLayer b ⟨x, hx⟩).trans
    (layerAt_node (nativeChainLayered D hS layer hLayer b) ⟨x, hx⟩).symm

theorem chainAddr_injOn (b : GBranch S.tree) (x y : Fin 1 × TTree.Path)
    (h : chainAddr D b x = chainAddr D b y) : x = y := by
  have h2 : x.2 = y.2 := List.append_cancel_left (congrArg Prod.snd h)
  exact Prod.ext (Subsingleton.elim _ _) h2

theorem tree_incoherency_eq (b : GBranch S.tree) :
    (layeredReconstruction D hS layer hLayer).incoherency
        ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) =
      (nativeChainLayered D hS layer hLayer b).incoherency
        ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) := by
  classical
  have hX : (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden := decodedTree_decodes _ _
  rw [tree_incoherency_eq_count hX, chainLinksAt_eq_map]
  have hsig : (nativeChainLayered D hS layer hLayer b).garden.sig 0 = nodeSign S.sig b.1 := rfl
  rw [hsig]
  have hbr : ∀ l ∈ (D.tree b).treeLinks (nodeSign S.sig b.1),
      l.1.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l.1.1).branching ∧
      l.2.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l.2.1).branching := by
    intro l hl
    exact ⟨(tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
      (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)⟩
  have hnd0 : ((D.tree b).treeLinks (nodeSign S.sig b.1)).Nodup :=
    nodup_of_flat_nodup (tree_links_flat_nodup _ _)
  have hnode : ∀ x : Fin 1 × TTree.Path,
      x.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree x.1).branching →
      (chainAddr D b x).2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree
        (chainAddr D b x).1).branching :=
    fun x hx => (chainContextBranch D hS b ⟨x.2, hx⟩).2
  have hnd : (((D.tree b).treeLinks (nodeSign S.sig b.1)).map
      (fun l => (chainAddr D b l.1, chainAddr D b l.2))).Nodup := by
    refine List.Nodup.map_on ?_ hnd0
    intro x hx y hy hxy
    exact Prod.ext (chainAddr_injOn D b _ _ (congrArg Prod.fst hxy)) (chainAddr_injOn D b _ _ (congrArg Prod.snd hxy))
  have hb : ∀ l ∈ ((D.tree b).treeLinks (nodeSign S.sig b.1)).map
      (fun l => (chainAddr D b l.1, chainAddr D b l.2)),
      l.1.2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree l.1.1).branching ∧
      l.2.2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree l.2.1).branching := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    exact ⟨hnode _ (hbr l0 hl0).1, hnode _ (hbr l0 hl0).2⟩
  rw [incoherency_eq_count_of _ _ hnd hb, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have e1 := chain_layerAt_of_mem D hS layer hLayer b l.1 (TTree.branching_subset_nodes _ (hbr l hl).1)
  have e2 := chain_layerAt_of_mem D hS layer hLayer b l.2 (TTree.branching_subset_nodes _ (hbr l hl).2)
  simp only [Function.comp, e1, e2]

end WaveTurbulence.VineA
