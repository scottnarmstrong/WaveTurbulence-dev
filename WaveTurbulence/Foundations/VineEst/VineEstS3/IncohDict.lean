/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.Molecule.LFTwist.LFSource
public import WaveTurbulence.Foundations.Molecule.LFTwist.LinkNaturality

/-! # The incoherency dictionary (R22 (4))

The incoherency index `rowTreeG` / `rowCoupleG` of a native row (a `LayeredGarden.incoherency` of the layered native
tree/couple) vanishes only if the object is coherent in the sense of `Links.CohOn` for the big layered garden
(`layeredReconstruction`) at the inflated position -- the form of `LFSource.treeCoherent` / `coupleCoherent`.
Hence `¬ CohOn ⟹ 1 ≤ g` (`one_le_rowTreeG_of_not_cohOn`, `one_le_rowCoupleG_of_not_cohOn`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  WaveTurbulence.Links

section
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- Zero incoherency index of the native tree ⟹ `CohOn` of the big layered garden. -/
theorem tree_cohOn_of_incoherency_zero (b : GBranch S.tree)
    (h : (nativeChainLayered D hS layer hLayer b).incoherency
      ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0) :
    CohOn (layeredReconstruction D hS layer hLayer)
      ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) := by
  have hX : (D.tree b).DecodesTree (nativeChainLayered D hS layer hLayer b).garden :=
    decodedTree_decodes _ _
  have hc := (tree_coherent_iff hX).1 h
  let a := inflatedPosition S D.tree b.toNode
  let f : (Fin 1 × Path) → (Fin w × Path) := fun z => addrExt a z.2
  have hf : RespectsAt f (0, []) := by
    intro q
    simp only [f, addrExt, List.nil_append, List.append_nil]
  have hm := LFTwist.chain_linksAt_map_local (D.tree b) f (0, []) hf (nodeSign S.sig b.1)
  have he : f (0, []) = a := by simp only [f, addrExt, List.append_nil]
  rw [he] at hm
  intro l hl
  rw [hm] at hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  have hlay : ∀ (x : Fin 1 × Path) (hx : x.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree x.1).nodes),
      layerAt (layeredReconstruction D hS layer hLayer) (f x) =
        layerAt (nativeChainLayered D hS layer hLayer b) x := by
    intro x hx
    have e1 := layerAt_node (nativeChainLayered D hS layer hLayer b) ⟨x, hx⟩
    have e2 := layerAt_node (layeredReconstruction D hS layer hLayer) (chainContextNode D hS b ⟨x, hx⟩)
    exact e2.trans e1.symm
  have hbr := fun hh : l' ∈ (D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0) =>
    (⟨(tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l', hh, Or.inl rfl⟩),
      (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l', hh, Or.inr rfl⟩)⟩ :
      l'.1.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l'.1.1).branching ∧
      l'.2.2 ∈ ((nativeChainLayered D hS layer hLayer b).garden.tree l'.2.1).branching)
  have hl'' : l' ∈ (D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0) := hl'
  obtain ⟨h1, h2⟩ := hbr hl''
  show layerAt _ (f l'.1) = layerAt _ (f l'.2)
  rw [hlay _ (TTree.branching_subset_nodes _ h1), hlay _ (TTree.branching_subset_nodes _ h2)]
  exact hc l' hl''
/-- Zero incoherency index of the native couple of `p` ⟹ `CohOn` of the big layered garden. -/
theorem couple_cohOn_of_incoherency_zero (p : SourcePair S)
    (h : (nativeCoupleLayered D hS layer hLayer p).incoherency (D.couple p).links = 0) :
    CohOn (layeredReconstruction D hS layer hLayer)
      ((D.couple p).linksAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) := by
  have hQ : (D.couple p).Decodes (nativeCoupleLayered D hS layer hLayer p).garden := by
    rw [nativeCoupleLayered_garden]; exact decodedCouple_decodes _
  have hc := (coherent_iff hQ).1 h
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
  intro l hl
  rw [hm] at hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
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
  have hl'' : l' ∈ (D.couple p).links := hl'
  obtain ⟨h1, h2, -⟩ := link_branching hQ hl''
  show layerAt _ (f l'.1) = layerAt _ (f l'.2)
  rw [hlay _ (TTree.branching_subset_nodes _ h1), hlay _ (TTree.branching_subset_nodes _ h2)]
  exact hc l' hl''
end

section Rows
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
  (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A non-coherent source tree at the branch carried by row `v` forces `1 ≤ g'` of the row. -/
theorem one_le_rowTreeG_of_not_cohOn (v : (assemblyShape hM9 B).VIdx)
    (h : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree (assemblyBranchOf hM9 B v).1).linksAt (nodeSign G.sig (assemblyBranchOf hM9 B v).1.1)
        (inflatedPosition G RD.tree (assemblyBranchOf hM9 B v).1.toNode))) :
    1 ≤ rowTreeG hM9 B RD hG layer hLayer v :=
  Nat.pos_of_ne_zero fun h0 => h (tree_cohOn_of_incoherency_zero RD hG layer hLayer _ h0)

/-- A non-coherent source couple at the pair carried by row `v` forces `1 ≤ g` of the row. -/
theorem one_le_rowCoupleG_of_not_cohOn (v : (assemblyShape hM9 B).VIdx)
    (h : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.couple (assemblyPairOf hM9 B hG v).1).linksAt
        (inflatedPosition G RD.tree ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode)
        (inflatedPosition G RD.tree ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode))) :
    1 ≤ rowCoupleG hM9 B RD hG layer hLayer v :=
  Nat.pos_of_ne_zero fun h0 => h (couple_cohOn_of_incoherency_zero RD hG layer hLayer _ h0)

end Rows

end WaveTurbulence.VineEstS3
