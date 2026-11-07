/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncohDict

/-! # P4-W2 (session 15, step 1): the converse of the incoherency dictionary

`tree_incoherency_zero_of_cohOn`, `couple_incoherency_zero_of_cohOn`: if the source tree / couple at the inflated position is
`CohOn` in the big layered garden, then the native incoherency index is `0` (the converses of
`VineEstS3.tree_cohOn_of_incoherency_zero` / `couple_cohOn_of_incoherency_zero`; the same proof read in the other direction).
`rowTreeG_eq_zero_of_cohOn`, `rowCoupleG_eq_zero_of_cohOn`: the row-level statements.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  WaveTurbulence.Links WaveTurbulence.VineEstS3

section
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- `CohOn` of the big layered garden at the inflated position ⟹ zero incoherency of the native tree. -/
theorem tree_incoherency_zero_of_cohOn (b : GBranch S.tree)
    (h : CohOn (layeredReconstruction D hS layer hLayer)
      ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))) :
    (nativeChainLayered D hS layer hLayer b).incoherency
      ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0 := by
  have hX : (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden :=
    decodedTree_decodes _ _
  refine (tree_coherent_iff hX).2 ?_
  let a := inflatedPosition S D.tree b.toNode
  let f : (Fin 1 × Path) → (Fin w × Path) := fun z => addrExt a z.2
  have hf : RespectsAt f (0, []) := by
    intro q
    simp only [f, addrExt, List.nil_append, List.append_nil]
  have hm := LFTwist.chain_linksAt_map_local (D.tree b) f (0, []) hf (nodeSign S.sig b.1)
  have he : f (0, []) = a := by simp only [f, addrExt, List.append_nil]
  rw [he] at hm
  have hlay : ∀ (x : Fin 1 × Path) (hx : x.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree x.1).nodes),
      layerAt (layeredReconstruction D hS layer hLayer) (f x) =
        layerAt (nativeChainLayered D hS layer hLayer b) x := by
    intro x hx
    have e1 := layerAt_node (nativeChainLayered D hS layer hLayer b) ⟨x, hx⟩
    have e2 := layerAt_node (layeredReconstruction D hS layer hLayer) (chainContextNode D hS b ⟨x, hx⟩)
    exact e2.trans e1.symm
  intro l' hl''
  obtain ⟨h1, h2⟩ : l'.1.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l'.1.1).branching ∧
      l'.2.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l'.2.1).branching :=
    ⟨(tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l', hl'', Or.inl rfl⟩),
      (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l', hl'', Or.inr rfl⟩)⟩
  have hmem : (f l'.1, f l'.2) ∈ (D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) := by
    rw [hm]; exact List.mem_map.mpr ⟨l', hl'', rfl⟩
  have hc := h _ hmem
  have hc' : layerAt (layeredReconstruction D hS layer hLayer) (f l'.1) =
      layerAt (layeredReconstruction D hS layer hLayer) (f l'.2) := hc
  rw [hlay _ (TTree.branching_subset_nodes _ h1), hlay _ (TTree.branching_subset_nodes _ h2)] at hc'
  exact hc'

/-- `CohOn` of the big layered garden at the inflated positions ⟹ zero incoherency of the native couple of `p`. -/
theorem couple_incoherency_zero_of_cohOn (p : SourcePair S)
    (h : CohOn (layeredReconstruction D hS layer hLayer)
      ((D.couple p).linksAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p.secondLeaf hS).toNode))) :
    (nativeCoupleLayered D hS layer hLayer p).incoherency (D.couple p).links = 0 := by
  have hQ : (D.couple p).Decodes (nativeCoupleLayered D hS layer hLayer p).garden := by
    rw [nativeCoupleLayered_garden]; exact decodedCouple_decodes _
  refine (coherent_iff hQ).2 ?_
  let a := inflatedPosition S D.tree (p.firstLeaf hS).toNode
  let b := inflatedPosition S D.tree (p.secondLeaf hS).toNode
  let f : (Fin 2 × Path) → (Fin w × Path) := fun z => addrExt (![a, b] z.1) z.2
  have hfa : RespectsAt f (0, []) := by
    intro q
    simp only [f, addrExt, List.nil_append, List.append_nil]
  have hfb : RespectsAt f (1, []) := by
    intro q
    simp only [f, addrExt, List.nil_append, List.append_nil]
  have hm := LFTwist.couple_linksAt_map_local (D.couple p) f (0, []) (1, []) hfa hfb
  have ea : f (0, []) = a := by simp only [f, addrExt, List.append_nil]; rfl
  have eb : f (1, []) = b := by simp only [f, addrExt, List.append_nil]; rfl
  rw [ea, eb] at hm
  have hlay : ∀ (x : Fin 2 × Path)
      (hx : x.2 ∈ ((nativeCoupleLayered D hS layer hLayer p).garden.tree x.1).nodes),
      layerAt (layeredReconstruction D hS layer hLayer) (f x) =
        layerAt (nativeCoupleLayered D hS layer hLayer p) x := by
    intro x hx
    have e1 := layerAt_node (nativeCoupleLayered D hS layer hLayer p) ⟨x, hx⟩
    have e2 := layerAt_node (layeredReconstruction D hS layer hLayer)
      ((nativeCoupleForest D hS p).nodeEmbedding ⟨x, hx⟩)
    have e3 : ((nativeCoupleForest D hS p).nodeEmbedding ⟨x, hx⟩).1 = f x := by
      obtain ⟨j, q⟩ := x
      fin_cases j <;> rfl
    rw [← e3]
    exact e2.trans e1.symm
  intro l' hl''
  obtain ⟨h1, h2, -⟩ := link_branching hQ hl''
  have hmem : (f l'.1, f l'.2) ∈ (D.couple p).linksAt a b := by
    rw [hm]; exact List.mem_map.mpr ⟨l', hl'', rfl⟩
  have hc' : layerAt (layeredReconstruction D hS layer hLayer) (f l'.1) =
      layerAt (layeredReconstruction D hS layer hLayer) (f l'.2) := h _ hmem
  rw [hlay _ (TTree.branching_subset_nodes _ h1), hlay _ (TTree.branching_subset_nodes _ h2)] at hc'
  exact hc'
end

section Rows
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
  (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A `CohOn` source tree at the branch carried by row `v` gives `g' = 0` of the row. -/
theorem rowTreeG_eq_zero_of_cohOn (v : (assemblyShape hM9 B).VIdx)
    (h : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree (assemblyBranchOf hM9 B v).1).linksAt (nodeSign G.sig (assemblyBranchOf hM9 B v).1.1)
        (inflatedPosition G RD.tree (assemblyBranchOf hM9 B v).1.toNode))) :
    rowTreeG hM9 B RD hG layer hLayer v = 0 :=
  tree_incoherency_zero_of_cohOn RD hG layer hLayer _ h

/-- A `CohOn` source couple at the pair carried by row `v` gives `g = 0` of the row. -/
theorem rowCoupleG_eq_zero_of_cohOn (v : (assemblyShape hM9 B).VIdx)
    (h : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.couple (assemblyPairOf hM9 B hG v).1).linksAt
        (inflatedPosition G RD.tree ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode)
        (inflatedPosition G RD.tree ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode))) :
    rowCoupleG hM9 B RD hG layer hLayer v = 0 :=
  couple_incoherency_zero_of_cohOn RD hG layer hLayer _ h
end Rows

end WaveTurbulence.VineEstS5C.P4.W2
