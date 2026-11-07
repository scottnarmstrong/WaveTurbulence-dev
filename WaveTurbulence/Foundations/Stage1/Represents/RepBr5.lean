/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepBr4
public import WaveTurbulence.Foundations.Molecule.LFTwist.LinkNaturality
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.IncohInst.Links.Omega
import Mathlib.Tactic

/-!
# S2 REPRESENTS: links of a native couple inside the reconstruction
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.LFTwist WaveTurbulence.Links

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The address map of the embedding of a native couple. -/
noncomputable def coupleAddr (p' : SourcePair S) (x : Fin 2 × TTree.Path) : Fin w × TTree.Path :=
  (((nativeCoupleForest D hS p').root x.1).1.1, ((nativeCoupleForest D hS p').root x.1).1.2 ++ x.2)

theorem coupleAddr_root (p' : SourcePair S) (j : Fin 2) :
    coupleAddr D hS p' (j, []) = inflatedPosition S D.tree
      (if j = 0 then (p'.firstLeaf hS).toNode else (p'.secondLeaf hS).toNode) := by
  rw [← couple_root_node D hS p' j]
  show _ = ((nativeCoupleForest D hS p').nodeEmbedding (GNode.root (nativeCoupleForest D hS p').shape j)).1
  rfl

theorem coupleAddr_respects (p' : SourcePair S) (j : Fin 2) :
    RespectsAt (coupleAddr D hS p') (j, []) := by
  intro q
  simp [coupleAddr, addrExt, List.append_assoc]

theorem coupleLinksAt_eq_map (p' : SourcePair S) :
    (D.couple p').linksAt (inflatedPosition S D.tree (p'.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p'.secondLeaf hS).toNode) =
      (D.couple p').links.map (fun l => (coupleAddr D hS p' l.1, coupleAddr D hS p' l.2)) := by
  have h0 := coupleAddr_root D hS p' 0
  have h1 := coupleAddr_root D hS p' 1
  simp only [if_true, one_ne_zero, if_false, Fin.isValue] at h0 h1
  rw [← h0, ← h1]
  exact couple_linksAt_map_local (D.couple p') (coupleAddr D hS p') (0, []) (1, [])
    (coupleAddr_respects D hS p' 0) (coupleAddr_respects D hS p' 1)

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem couple_layerAt (p' : SourcePair S) (a : GNode (nativeCoupleForest D hS p').shape) :
    layerAt (layeredReconstruction D hS layer hLayer) (coupleAddr D hS p' a.1) =
      (nativeCoupleLayered D hS layer hLayer p').layer a :=
  layerAt_node (layeredReconstruction D hS layer hLayer) ((nativeCoupleForest D hS p').nodeEmbedding a)

theorem coupleAddr_injOn (p' : SourcePair S) (a b : GNode (nativeCoupleForest D hS p').shape)
    (h : coupleAddr D hS p' a.1 = coupleAddr D hS p' b.1) : a.1 = b.1 := by
  have h' : ((nativeCoupleForest D hS p').nodeEmbedding a).1 =
      ((nativeCoupleForest D hS p').nodeEmbedding b).1 := h
  have := (nativeCoupleForest D hS p').nodeEmbedding.injective (Subtype.ext h')
  exact congrArg Subtype.val this

theorem couple_layerAt_of_mem (p' : SourcePair S) (x : Fin 2 × TTree.Path)
    (hx : x.2 ∈ ((nativeCoupleLayered D hS layer hLayer p').garden.tree x.1).nodes) :
    layerAt (layeredReconstruction D hS layer hLayer) (coupleAddr D hS p' x) =
      layerAt (nativeCoupleLayered D hS layer hLayer p') x := by
  have h1 := couple_layerAt D hS layer hLayer p' ⟨x, hx⟩
  have h2 := layerAt_node (nativeCoupleLayered D hS layer hLayer p') ⟨x, hx⟩
  exact h1.trans h2.symm

theorem couple_incoherency_eq (p' : SourcePair S) :
    (layeredReconstruction D hS layer hLayer).incoherency
        ((D.couple p').linksAt (inflatedPosition S D.tree (p'.firstLeaf hS).toNode)
          (inflatedPosition S D.tree (p'.secondLeaf hS).toNode)) =
      (nativeCoupleLayered D hS layer hLayer p').incoherency (D.couple p').links := by
  classical
  have hQ := couple_decodes D hS layer hLayer p'
  rw [incoherency_eq_count hQ, coupleLinksAt_eq_map]
  have hbr : ∀ l ∈ (D.couple p').links,
      l.1.2 ∈ ((nativeCoupleLayered D hS layer hLayer p').garden.tree l.1.1).branching ∧
      l.2.2 ∈ ((nativeCoupleLayered D hS layer hLayer p').garden.tree l.2.1).branching :=
    fun l hl => ⟨(link_branching hQ hl).1, (link_branching hQ hl).2.1⟩
  have hnd0 : (D.couple p').links.Nodup := nodup_of_flat_nodup (couple_links_flat_nodup _)
  have hnode : ∀ x : Fin 2 × TTree.Path,
      x.2 ∈ ((nativeCoupleLayered D hS layer hLayer p').garden.tree x.1).branching →
      (coupleAddr D hS p' x).2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree
        (coupleAddr D hS p' x).1).branching :=
    fun x hx => (coupleContextBranch D hS p' ⟨x, hx⟩).2
  have hnd : ((D.couple p').links.map
      (fun l => (coupleAddr D hS p' l.1, coupleAddr D hS p' l.2))).Nodup := by
    refine List.Nodup.map_on ?_ hnd0
    intro x hx y hy hxy
    have h1 := coupleAddr_injOn D hS p' ⟨x.1, TTree.branching_subset_nodes _ (hbr x hx).1⟩
      ⟨y.1, TTree.branching_subset_nodes _ (hbr y hy).1⟩ (congrArg Prod.fst hxy)
    have h2 := coupleAddr_injOn D hS p' ⟨x.2, TTree.branching_subset_nodes _ (hbr x hx).2⟩
      ⟨y.2, TTree.branching_subset_nodes _ (hbr y hy).2⟩ (congrArg Prod.snd hxy)
    exact Prod.ext h1 h2
  have hb : ∀ l ∈ (D.couple p').links.map
      (fun l => (coupleAddr D hS p' l.1, coupleAddr D hS p' l.2)),
      l.1.2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree l.1.1).branching ∧
      l.2.2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree l.2.1).branching := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    exact ⟨hnode _ (hbr l0 hl0).1, hnode _ (hbr l0 hl0).2⟩
  rw [incoherency_eq_count_of _ _ hnd hb, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have e1 := couple_layerAt_of_mem D hS layer hLayer p' l.1 (TTree.branching_subset_nodes _ (hbr l hl).1)
  have e2 := couple_layerAt_of_mem D hS layer hLayer p' l.2 (TTree.branching_subset_nodes _ (hbr l hl).2)
  simp only [Function.comp, e1, e2]

end WaveTurbulence.Represents
