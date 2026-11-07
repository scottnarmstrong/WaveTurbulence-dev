/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound5
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowCanon

/-! # ZP-SURJ: coherence of the native exceptional objects of a reconstruction -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.VineEstS4
  WaveTurbulence.LGSpine

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hL : IsLayering (D.garden hS) layer)

theorem layerRec_couple_all (q : SourcePair S) (i : Fin 2) (r : Path) :
    layerAt (layeredReconstruction D hS layer hL) (addrExt (coupleRoot D hS q i) r) =
      layerAt (nativeCoupleLayered D hS layer hL q) (i, r) := by
  have hd := D.garden_decodes hS
  have hEM := reconstruction_coupleEmb D hS hd q
  have EQ := Embeds.of_decodes (decodedCouple_decodes (D.couple q))
  have hg : (nativeCoupleLayered D hS layer hL q).garden = decodedCouple (D.couple q) :=
    nativeCoupleLayered_garden _ _ _ _ _
  by_cases h : r ∈ ((nativeCoupleLayered D hS layer hL q).garden.tree i).nodes
  · have h' : r ∈ ((decodedCouple (D.couple q)).tree i).nodes := by rw [← hg]; exact h
    exact (layerAt_nativeCouple D hS layer hL q (i, r) h').symm
  · have e1 : layerAt (nativeCoupleLayered D hS layer hL q) (i, r) = 0 := by unfold layerAt; exact dif_neg h
    have e2 : layerAt (layeredReconstruction D hS layer hL) (addrExt (coupleRoot D hS q i) r) = 0 := by
      unfold layerAt
      refine dif_neg (fun hh => h ?_)
      have h' : r ∈ ((decodedCouple (D.couple q)).tree i).nodes := by
        fin_cases i
        · exact (node_iff_of_subtree EQ.nodeA EQ.treeA r).1.2 ((node_iff_of_subtree hEM.nodeA hEM.treeA r).1.1 hh)
        · exact (node_iff_of_subtree EQ.nodeB EQ.treeB r).1.2 ((node_iff_of_subtree hEM.nodeB hEM.treeB r).1.1 hh)
      rw [hg]; exact h'
    rw [e1, e2]

theorem cohOn_of_native_pattern (q : SourcePair S) {pa pb : ℕ}
    (h : LayerPatternN (nativeCoupleLayered D hS layer hL q) pa pb (D.couple q) ((0 : Fin 2), ([] : Path))
      ((1 : Fin 2), ([] : Path))) :
    CohOn (layeredReconstruction D hS layer hL)
      ((D.couple q).linksAt (coupleRoot D hS q 0) (coupleRoot D hS q 1)) := by
  have := (layerPatternN_reloc (H1 := nativeCoupleLayered D hS layer hL q)
    (H2 := layeredReconstruction D hS layer hL) pa pb (D.couple q) ((0 : Fin 2), ([] : Path))
    ((1 : Fin 2), ([] : Path)) indep_root2 (coupleRoot D hS q 0) (coupleRoot D hS q 1)
    (fun r => by simpa [addrExt] using layerRec_couple_all D hS layer hL q 0 r)
    (fun r => by simpa [addrExt] using layerRec_couple_all D hS layer hL q 1 r)).2 h
  exact this.1

theorem coupleCnt_zero_of_cohOn (q : SourcePair S) (LG : LayeredGarden w)
    (h : CohOn LG ((D.couple q).linksAt (coupleRoot D hS q 0) (coupleRoot D hS q 1))) :
    coupleCnt D hS LG q = 0 := by
  unfold coupleCnt linkCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro l hl
  simpa using h l hl

theorem treeCnt_zero_of_cohOn (b : GBranch S.tree) (LG : LayeredGarden w)
    (h : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))) :
    treeCnt D LG b = 0 := by
  unfold treeCnt linkCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro l hl
  simpa using h l hl

theorem cohOn_tree_of_native_pattern (b : GBranch S.tree) {pa : ℕ}
    (h : TreePatternN (nativeChainLayered D hS layer hL b) pa (D.tree b) (nodeSign S.sig b.1) ((0 : Fin 1), ([] : Path))) :
    CohOn (layeredReconstruction D hS layer hL)
      ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) := by
  have hlay : ∀ r ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes,
      layerAt (layeredReconstruction D hS layer hL) (addrExt (inflatedPosition S D.tree b.toNode) r) =
        layerAt (nativeChainLayered D hS layer hL b) ((0 : Fin 1), r) := fun r hr =>
    (layerAt_nativeTree D hS layer hL b ((0 : Fin 1), r) hr).symm
  exact ((treePatternN_native (H := layeredReconstruction D hS layer hL) (a := inflatedPosition S D.tree b.toNode)
    (X := D.tree b) (ζ := nodeSign S.sig b.1) (LX := nativeChainLayered D hS layer hL b) pa hlay).2 h).1

end WaveTurbulence.ZpSurj
