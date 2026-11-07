/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed2

/-! # A canonical reconstructed garden has all its coherent rows coherent (V5 Step 4b, step 1)

`rowsCoh_of_canonical`: if the reconstructed garden `layeredReconstruction RD hG layer hLayer` is canonical
(`IsCanonGC (p+1)`), then every regional couple and every interior tree with incoherency count `0` is a coherent
embedded object (`IsCoherentCoupleAt`, `IsCoherentTreeAt`), witnessed by the reconstructed garden itself, with the
parent-core layers `pairQ`, `branchQ`.  This is TARGET L899-L905 applied inside a canonical garden.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.LGSpine VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The parent layer of the position of an attached node is the layer of the core of its parent. -/
theorem parAt_attached (p : ℕ) (x : GNode G.tree) (hn : x.1.2 ≠ []) :
    parAt (layeredReconstruction RD hG layer hLayer) p (inflatedPosition G RD.tree x) =
      layer (RD.coreBranch hG (x.parent hn)).toNode := by
  have h2 : attachedNode RD hG x = (RD.coreBranch hG (x.parent hn)).child (List.getLast x.1.2 hn) := by
    rw [← attached_child_eq, Mole.parent_child_eq_node x hn]
  have h3 : inflatedPosition G RD.tree x = addrExt (RD.coreBranch hG (x.parent hn)).1 [List.getLast x.1.2 hn] :=
    congrArg Subtype.val h2
  rw [h3]
  have hm : (addrExt (RD.coreBranch hG (x.parent hn)).1 [List.getLast x.1.2 hn]).2 ∈
      ((layeredReconstruction RD hG layer hLayer).garden.tree
        (addrExt (RD.coreBranch hG (x.parent hn)).1 [List.getLast x.1.2 hn]).1).nodes := by
    have := (attachedNode RD hG x).2
    rw [show (attachedNode RD hG x).1 = _ from h3] at this
    exact this
  rw [parAt_child _ _ _ hm]
  exact layerAt_node (layeredReconstruction RD hG layer hLayer) (RD.coreBranch hG (x.parent hn)).toNode

omit hLayer in
theorem canonGC_of_canonicalObject {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (hc : CanonicalObject p kind LG) :
    IsCanonGC (p + 1) LG := by
  cases hc with
  | garden hc => exact ⟨hc.2.1, Or.inl ⟨hc.1, hc.2.2.1⟩, hc.2.2.2⟩
  | couple hc => exact (Canon.isCanonGC_iff_isCanonC _ _).2 hc

theorem couple_coherent_of_canonical (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (q : SourcePair G) (hn1 : (q.firstLeaf hG).toNode.1.2 ≠ []) (hn2 : (q.secondLeaf hG).toNode.1.2 ≠ [])
    (hc : coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) q = 0) :
    IsCoherentCoupleAt p (pairQ RD hG layer q).1 (pairQ RD hG layer q).2 (RD.couple q)
      (nativeCoupleLayered RD hG layer hLayer q) := by
  have hd := RD.garden_decodes hG
  have hQ : (RD.couple q).Decodes (nativeCoupleLayered RD hG layer hLayer q).garden := by
    rw [nativeCoupleLayered_garden]
    exact decodedCouple_decodes _
  refine ⟨RD.couple_wf q, hQ, w, layeredReconstruction RD hG layer hLayer, coupleRoot RD hG q 0,
    coupleRoot RD hG q 1, hcan, reconstruction_coupleEmb RD hG hd q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := RD.decodedNode_sign hG hd (q.firstLeaf hG).toNode
    exact h.trans (sourcePair_first_sign G hG q)
  · have h := RD.decodedNode_sign hG hd (q.secondLeaf hG).toNode
    exact h.trans (sourcePair_second_sign G hG q)
  · intro l hl
    unfold coupleCnt linkCount at hc
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hc
    simpa using hc l hl
  · exact (parAt_attached RD hG layer hLayer p _ hn1).trans (by simp [pairQ, parentCoreLayer, hn1])
  · exact (parAt_attached RD hG layer hLayer p _ hn2).trans (by simp [pairQ, parentCoreLayer, hn2])
  · intro z
    have h1 := layerAt_nativeCouple RD hG layer hLayer q z.1 z.2
    have h2 := layerAt_node (nativeCoupleLayered RD hG layer hLayer q) z
    refine h2.symm.trans (h1.trans ?_)
    obtain ⟨⟨i, r⟩, hz⟩ := z
    fin_cases i <;> rfl

theorem tree_coherent_of_canonical (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (c : GBranch G.tree) (hn : c.toNode.1.2 ≠ [])
    (hc : treeCnt RD (layeredReconstruction RD hG layer hLayer) c = 0) :
    IsCoherentTreeAt p (branchQ RD hG layer c).1 (branchQ RD hG layer c).2 (RD.tree c)
      (nativeChainLayered RD hG layer hLayer c) := by
  have hd := RD.garden_decodes hG
  have hX : (RD.tree c).DecodesTree (nativeChainLayered RD hG layer hLayer c).garden := decodedTree_decodes _ _
  have hsig : (nativeChainLayered RD hG layer hLayer c).garden.sig 0 = nodeSign G.sig c.1 := rfl
  refine ⟨RD.tree_wf c, hX, w, layeredReconstruction RD hG layer hLayer, inflatedPosition G RD.tree c.toNode,
    node3 (fun i => RD.inflateNode hG (c.child i)), hcan, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsig]
    exact reconstruction_chainEmb RD hG hd c
  · rw [hsig]
    exact (RD.decodedNode_sign hG hd c.toNode)
  · rw [hsig]
    intro l hl
    unfold treeCnt linkCount at hc
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hc
    simpa using hc l hl
  · exact (parAt_attached RD hG layer hLayer p _ hn).trans (by simp [branchQ, parentCoreLayer, hn])
  · exact layerAt_node (layeredReconstruction RD hG layer hLayer) (RD.coreBranch hG c).toNode
  · intro z
    have h2 := layerAt_node (layeredReconstruction RD hG layer hLayer) (chainContextNode RD hG c z)
    exact h2.symm

/-- **A canonical reconstructed garden has coherent rows.** -/
theorem rowsCoh_of_canonical (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (p : ℕ)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer)) : RowsCoh RD hG layer hLayer p U a := by
  refine ⟨fun q hq hc => ?_, fun c hcU hc => ?_⟩
  · have hr := clRegionalPair_realization hG q hq
    have hp := pairLeaf_ne (a := a) hG ⟨q, hq⟩
    exact couple_coherent_of_canonical RD hG layer hLayer p hcan q
      (cl_realization_parent hB R _ hr.1 hp.1).1 (cl_realization_parent hB R _ hr.2 hp.2).1 hc
  · have hbr := (branch_mem_clRealizationNodes c).mpr (Finset.mem_erase.mp hcU).2
    have hne := interior_ne (R := R) (⟨c, hcU⟩ : ↥(clInteriorBranches R))
    exact tree_coherent_of_canonical RD hG layer hLayer p hcan c (cl_realization_parent hB R _ hbr hne).1 hc

end WaveTurbulence.VineEstS4
