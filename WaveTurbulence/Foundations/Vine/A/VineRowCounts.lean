/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineTreeIndex
public import WaveTurbulence.Foundations.Molecule.LFTwist.DecodedLayered
public import WaveTurbulence.Foundations.Molecule.LFTwist.ChoiceGeometry
/-! Counts of actual embedded regular rows at arbitrary decoded layerings.
The embedding proofs follow S2 RepBr5 and RepBr7, copied with source hashes. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset TTree Reg Reg.Skeleton RegRed LFTwist Links
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
theorem couple_incoherency_count (p' : SourcePair S) :
    (layeredReconstruction D hS layer hLayer).incoherency
        ((D.couple p').linksAt (inflatedPosition S D.tree (p'.firstLeaf hS).toNode)
          (inflatedPosition S D.tree (p'.secondLeaf hS).toNode)) =
      ((D.couple p').links.filter fun l =>
        layerAt (layeredReconstruction D hS layer hLayer) (coupleAddr D hS p' l.1) ≠
        layerAt (layeredReconstruction D hS layer hLayer) (coupleAddr D hS p' l.2)).length := by
  classical
  have hQ : (D.couple p').Decodes (nativeCoupleLayered D hS layer hLayer p').garden := by
    rw [nativeCoupleLayered_garden]
    exact decodedCouple_decodes _
  rw [coupleLinksAt_eq_map]
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
  rfl

theorem tree_incoherency_count (b : GBranch S.tree) :
    (layeredReconstruction D hS layer hLayer).incoherency
        ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) =
      (((D.tree b).treeLinks (nodeSign S.sig b.1)).filter fun l =>
        layerAt (layeredReconstruction D hS layer hLayer) (chainAddr D b l.1) ≠
        layerAt (layeredReconstruction D hS layer hLayer) (chainAddr D b l.2)).length := by
  classical
  have hX : (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden := decodedTree_decodes _ _
  rw [chainLinksAt_eq_map]
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
  rfl

/-- Decode the source couple row without changing the arbitrary original layered garden. -/
theorem decoded_couple_incoherency_count (LG : LayeredGarden w) (hd : D.Decodes hS LG.garden)
    (q : SourcePair S) :
    LG.incoherency ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (q.secondLeaf hS).toNode)) =
      ((D.couple q).links.filter fun l => layerAt LG (coupleAddr D hS q l.1) ≠
        layerAt LG (coupleAddr D hS q l.2)).length := by
  simpa only [decodedLayered_eq D hS LG hd] using
    couple_incoherency_count D hS (decodedLayer D hS LG hd) (decodedLayer_isLayering D hS LG hd) q

/-- Decode the source tree row without changing the arbitrary original layered garden. -/
theorem decoded_tree_incoherency_count (LG : LayeredGarden w) (hd : D.Decodes hS LG.garden)
    (b : GBranch S.tree) :
    LG.incoherency ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) =
      (((D.tree b).treeLinks (nodeSign S.sig b.1)).filter fun l =>
        layerAt LG (chainAddr D b l.1) ≠ layerAt LG (chainAddr D b l.2)).length := by
  simpa only [decodedLayered_eq D hS LG hd] using
    tree_incoherency_count D hS (decodedLayer D hS LG hd) (decodedLayer_isLayering D hS LG hd) b

/-- The concrete native-couple address is precisely the source's named root extension. -/
theorem coupleAddr_eq_root (q : SourcePair S) (x : Fin 2 × Path) :
    coupleAddr D hS q x = addrExt (coupleRoot D hS q x.1) x.2 := by
  rcases x with ⟨i, r⟩
  fin_cases i <;> rfl

end WaveTurbulence.VineA
