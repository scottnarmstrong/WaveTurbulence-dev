/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.Molecule.LFTwist.LinkNaturality
public import WaveTurbulence.Foundations.Molecule.LFTwist.ChoiceGeometry

/-! # The incoherency index of a native row as a global link count (V5 Step 4b, step 1 bridge)

The native layered couple (tree) of a row inherits its layering from the reconstructed garden:
`layerAt (nativeCoupleLayered ..) (i,r) = layerAt big (addrExt (coupleRoot .. i) r)` (`layerAt_nativeCouple`), so its
incoherency index is the number `coupleCnt` of links `(𝔫,𝔫')` of the couple, written at the global addresses, whose two
nodes lie in different layers of the reconstructed garden (`incoherency_native_couple`, `..._tree`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg TTree

variable {w : ℕ} {S : Garden w}

/-- The number of links whose two nodes lie in different layers. -/
@[expose] def linkCount (LG : LayeredGarden w) (L : List (Address w × Address w)) : ℕ :=
  (L.filter fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)).length

/-- Global address of a node of the native couple of the pair `q`. -/
@[expose] noncomputable def coupleAddr (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S) (z : Fin 2 × Path) : Address w :=
  addrExt (coupleRoot D hS q z.1) z.2

/-- Global address of a node of the native tree of the branch `b`. -/
@[expose] def treeAddr (D : ReconstructionData S) (b : GBranch S.tree) (z : Fin 1 × Path) : Address w :=
  addrExt (inflatedPosition S D.tree b.toNode) z.2

/-- The incoherency count of the couple of `q` in the layered garden `LG`. -/
@[expose] noncomputable def coupleCnt (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden w)
    (q : SourcePair S) : ℕ :=
  linkCount LG ((D.couple q).linksAt (coupleRoot D hS q 0) (coupleRoot D hS q 1))

/-- The incoherency count of the tree of `b` in the layered garden `LG`. -/
@[expose] noncomputable def treeCnt (D : ReconstructionData S) (LG : LayeredGarden w) (b : GBranch S.tree) : ℕ :=
  linkCount LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))

theorem layerAt_nativeCouple (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (q : SourcePair S) (z : Fin 2 × Path)
    (hz : z.2 ∈ ((decodedCouple (D.couple q)).tree z.1).nodes) :
    layerAt (nativeCoupleLayered D hS layer hLayer q) z =
      layerAt (layeredReconstruction D hS layer hLayer) (coupleAddr D hS q z) := by
  obtain ⟨i, r⟩ := z
  have h1 := layerAt_node (nativeCoupleLayered D hS layer hLayer q) ⟨(i, r), hz⟩
  have h2 := layerAt_node (layeredReconstruction D hS layer hLayer)
    ((nativeCoupleForest D hS q).nodeEmbedding ⟨(i, r), hz⟩)
  refine h1.trans (Eq.trans ?_ (h2.symm.trans ?_))
  · rfl
  · fin_cases i <;> rfl

theorem layerAt_nativeTree (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) (z : Fin 1 × Path)
    (hz : z.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree z.1).nodes) :
    layerAt (nativeChainLayered D hS layer hLayer b) z =
      layerAt (layeredReconstruction D hS layer hLayer) (treeAddr D b z) := by
  obtain ⟨i, r⟩ := z
  have h1 := layerAt_node (nativeChainLayered D hS layer hLayer b) ⟨(i, r), hz⟩
  have h2 := layerAt_node (layeredReconstruction D hS layer hLayer) (chainContextNode D hS b ⟨(i, r), hz⟩)
  refine h1.trans (Eq.trans ?_ (h2.symm.trans ?_))
  · rfl
  · fin_cases i; rfl

/-- The global link count as a count over the couple-local links. -/
theorem coupleCnt_eq_local (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden w) (q : SourcePair S) :
    coupleCnt D hS LG q = ((D.couple q).links.filter fun l =>
      decide (layerAt LG (coupleAddr D hS q l.1) ≠ layerAt LG (coupleAddr D hS q l.2))).length := by
  let f : Fin 2 × Path → Address w := coupleAddr D hS q
  have h0 : RespectsAt f ((0 : Fin 2), []) := by
    intro p; simp [f, coupleAddr, addrExt, coupleRoot]
  have h1 : RespectsAt f ((1 : Fin 2), []) := by
    intro p; simp [f, coupleAddr, addrExt, coupleRoot]
  have hm := couple_linksAt_map_local (D.couple q) f _ _ h0 h1
  have e0 : f ((0 : Fin 2), []) = coupleRoot D hS q 0 := by simp [f, coupleAddr, addrExt]
  have e1 : f ((1 : Fin 2), []) = coupleRoot D hS q 1 := by simp [f, coupleAddr, addrExt]
  rw [e0, e1] at hm
  unfold coupleCnt linkCount
  rw [hm, List.filter_map, List.length_map]
  rfl

/-- The global link count of a tree as a count over the tree-local links. -/
theorem treeCnt_eq_local (D : ReconstructionData S) (LG : LayeredGarden w) (b : GBranch S.tree) :
    treeCnt D LG b = (((D.tree b).treeLinks (nodeSign S.sig b.1)).filter fun l =>
      decide (layerAt LG (treeAddr D b l.1) ≠ layerAt LG (treeAddr D b l.2))).length := by
  let a := inflatedPosition S D.tree b.toNode
  let f : Fin 1 × Path → Address w := treeAddr D b
  have h0 : RespectsAt f ((0 : Fin 1), []) := by
    intro p; simp [f, treeAddr, addrExt]
  have hm := chain_linksAt_map_local (D.tree b) f _ h0 (nodeSign S.sig b.1)
  have e0 : f ((0 : Fin 1), []) = a := by simp [f, treeAddr, addrExt, a]
  rw [e0] at hm
  unfold treeCnt linkCount
  rw [hm, List.filter_map, List.length_map]
  rfl

/-- The endpoints of the couple-local links are nodes of the decoded couple. -/
theorem couple_link_nodes (D : ReconstructionData S) (q : SourcePair S) {l : (Fin 2 × Path) × Fin 2 × Path}
    (hl : l ∈ (D.couple q).links) :
    l.1.2 ∈ ((decodedCouple (D.couple q)).tree l.1.1).nodes ∧ l.2.2 ∈ ((decodedCouple (D.couple q)).tree l.2.1).nodes := by
  have hb := link_branching (decodedCouple_decodes (D.couple q)) hl
  exact ⟨TTree.branching_subset_nodes _ hb.1, TTree.branching_subset_nodes _ hb.2.1⟩

/-- The endpoints of the tree-local links are nodes of the plugged tree. -/
theorem tree_link_nodes (D : ReconstructionData S) (b : GBranch S.tree)
    {l : (Fin 1 × Path) × Fin 1 × Path} (hl : l ∈ (D.tree b).treeLinks (nodeSign S.sig b.1)) :
    l.1.2 ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes ∧ l.2.2 ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes := by
  have hX : (D.tree b).DecodesTree (decodedTree (D.tree b) (nodeSign S.sig b.1)) := decodedTree_decodes _ _
  have hb1 := (tree_mem_pairEndpoints_links_iff hX l.1).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩)
  have hb2 := (tree_mem_pairEndpoints_links_iff hX l.2).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)
  exact ⟨TTree.branching_subset_nodes _ hb1, TTree.branching_subset_nodes _ hb2⟩

/-- **Couple bridge.**  The incoherency index of the native layered couple is the global link count. -/
theorem incoherency_native_couple (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (q : SourcePair S) :
    (nativeCoupleLayered D hS layer hLayer q).incoherency (D.couple q).links =
      coupleCnt D hS (layeredReconstruction D hS layer hLayer) q := by
  have hQ : (D.couple q).Decodes (nativeCoupleLayered D hS layer hLayer q).garden := by
    rw [nativeCoupleLayered_garden]
    exact decodedCouple_decodes _
  rw [incoherency_eq_count hQ]
  let f : Fin 2 × Path → Address w := coupleAddr D hS q
  have h0 : RespectsAt f ((0 : Fin 2), []) := by
    intro p; simp [f, coupleAddr, addrExt, coupleRoot]
  have h1 : RespectsAt f ((1 : Fin 2), []) := by
    intro p; simp [f, coupleAddr, addrExt, coupleRoot]
  have hm := couple_linksAt_map_local (D.couple q) f _ _ h0 h1
  have e0 : f ((0 : Fin 2), []) = coupleRoot D hS q 0 := by simp [f, coupleAddr, addrExt]
  have e1 : f ((1 : Fin 2), []) = coupleRoot D hS q 1 := by simp [f, coupleAddr, addrExt]
  rw [e0, e1] at hm
  unfold coupleCnt linkCount
  rw [hm, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have hb := link_branching hQ hl
  have n1 := layerAt_nativeCouple D hS layer hLayer q l.1 (TTree.branching_subset_nodes _ hb.1)
  have n2 := layerAt_nativeCouple D hS layer hLayer q l.2 (TTree.branching_subset_nodes _ hb.2.1)
  simp only [Function.comp, n1, n2]
  rfl

/-- **Tree bridge.** -/
theorem incoherency_native_tree (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) :
    (nativeChainLayered D hS layer hLayer b).incoherency
        ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) =
      treeCnt D (layeredReconstruction D hS layer hLayer) b := by
  have hX : (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden :=
    decodedTree_decodes _ _
  rw [tree_incoherency_eq_count hX]
  let a := inflatedPosition S D.tree b.toNode
  let f : Fin 1 × Path → Address w := treeAddr D b
  have h0 : RespectsAt f ((0 : Fin 1), []) := by
    intro p; simp [f, treeAddr, addrExt]
  have hm := chain_linksAt_map_local (D.tree b) f _ h0 (nodeSign S.sig b.1)
  have e0 : f ((0 : Fin 1), []) = a := by simp [f, treeAddr, addrExt, a]
  rw [e0] at hm
  have hsig : (nativeChainLayered D hS layer hLayer b).garden.sig 0 = nodeSign S.sig b.1 := rfl
  rw [hsig]
  unfold treeCnt linkCount
  rw [hm, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have hb1 := (tree_mem_pairEndpoints_links_iff hX l.1).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩)
  have hb2 := (tree_mem_pairEndpoints_links_iff hX l.2).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)
  have n1 := layerAt_nativeTree D hS layer hLayer b l.1 (TTree.branching_subset_nodes _ hb1)
  have n2 := layerAt_nativeTree D hS layer hLayer b l.2 (TTree.branching_subset_nodes _ hb2)
  simp only [Function.comp, n1, n2]
  rfl

end WaveTurbulence.VineEstS4
