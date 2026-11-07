/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound1

/-! # ZP-SURJ soundness: the native couple of a construction is a pattern datum -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (con : LFConstruction s ε)

/-- The native exceptional couple of a construction. -/
@[expose] noncomputable def conLQ : LayeredGarden 2 :=
  nativeCoupleLayered con.data (s.chosen_plain ε) con.outLayer con.out_isLayering (s.pairs ε s.exceptional)

/-- The native exceptional tree of a construction. -/
@[expose] noncomputable def conLX : LayeredGarden 1 :=
  nativeChainLayered con.data (s.chosen_plain ε) con.outLayer con.out_isLayering (s.branches ε s.placement.lower)

theorem conLQ_decodes : con.newCouple.Decodes (conLQ con).garden := by
  have hFD : con.data.couple (s.pairs ε s.exceptional) = con.newCouple := Function.update_self _ _ _
  have hg : (conLQ con).garden = decodedCouple (con.data.couple (s.pairs ε s.exceptional)) :=
    nativeCoupleLayered_garden _ _ _ _ _
  rw [hg, hFD]
  exact decodedCouple_decodes _

theorem conLX_decodes : con.newTree.DecodesTree (conLX con).garden := by
  have hFD : con.data.tree (s.branches ε s.placement.lower) = con.newTree := Function.update_self _ _ _
  change con.newTree.DecodesTree (decodedTree (con.data.tree (s.branches ε s.placement.lower))
    (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1))
  rw [hFD]
  exact decodedTree_decodes _ _

theorem conLX_sig : (conLX con).garden.sig 0 = srcSign s ε := rfl

theorem conMid_embeds : Embeds (conMid con).garden con.newCouple (cA s ε) (cB s ε) := by
  have h := con.coupleInsertion.newEmbedding
  rw [coupleRoot_zero, coupleRoot_one] at h
  exact h

theorem conLQ_layer (r : Path) :
    layerAt (conLQ con) ((0 : Fin 2), r) = layerAt (conMid con) (addrExt (cA s ε) r) ∧
    layerAt (conLQ con) ((1 : Fin 2), r) = layerAt (conMid con) (addrExt (cB s ε) r) := by
  have EQ := Embeds.of_decodes (conLQ_decodes con)
  have hEM := conMid_embeds con
  have key : ∀ (i : Fin 2) (c : Fin w × Path)
      (hiff : (addrExt c r).2 ∈ ((conMid con).garden.tree (addrExt c r).1).nodes ↔ r ∈ ((conLQ con).garden.tree i).nodes)
      (hc : c = coupleRoot (s.midData ε con.newCouple con.couple_wf) (s.chosen_plain ε) (s.pairs ε s.exceptional) i),
      layerAt (conLQ con) (i, r) = layerAt (conMid con) (addrExt c r) := by
    intro i c hiff hc
    by_cases h : r ∈ ((conLQ con).garden.tree i).nodes
    · have h1 := VineEstS4.layerAt_nativeCouple con.data (s.chosen_plain ε) con.outLayer con.out_isLayering
        (s.pairs ε s.exceptional) (i, r) h
      have h2 := con_layer_couple con i r
      subst hc
      exact h1.trans h2
    · have e1 : layerAt (conLQ con) (i, r) = 0 := by unfold layerAt; exact dif_neg h
      have e2 : layerAt (conMid con) (addrExt c r) = 0 := by
        unfold layerAt; exact dif_neg (fun hh => h (hiff.1 hh))
      rw [e1, e2]
  exact ⟨key 0 (cA s ε) ((node_iff_of_subtree hEM.nodeA hEM.treeA r).1.trans
      (node_iff_of_subtree EQ.nodeA EQ.treeA r).1.symm) (coupleRoot_zero s ε).symm,
    key 1 (cB s ε) ((node_iff_of_subtree hEM.nodeB hEM.treeB r).1.trans
      (node_iff_of_subtree EQ.nodeB EQ.treeB r).1.symm) (coupleRoot_one s ε).symm⟩

theorem conLQ_pattern :
    LayerPatternN (conLQ con) (parAt (s.base ε) p (cA s ε)) (parAt (s.base ε) p (cB s ε)) con.newCouple
      ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) := by
  have hEM := conMid_embeds con
  have hout := con.coupleInsertion.outside
  rw [coupleRoot_zero, coupleRoot_one] at hout
  have hpat := con.coupleInsertion.pattern
  rw [coupleRoot_zero, coupleRoot_one] at hpat
  rw [layerPattern_eq_N] at hpat
  have hpa : parAt (s.base ε) p (cA s ε) = parAt (conMid con) p (cA s ε) :=
    hout.parAt_eq_a hEM.indep exc_embB.nodeA hEM.nodeA
  have hpb : parAt (s.base ε) p (cB s ε) = parAt (conMid con) p (cB s ε) :=
    hout.parAt_eq_b hEM.indep exc_embB.nodeB hEM.nodeB
  rw [hpa, hpb]
  refine (layerPatternN_reloc _ _ _ (cA s ε) (cB s ε) hEM.indep _ _ ?_ ?_).2 hpat
  · intro r
    exact (conLQ_layer con r).1
  · intro r
    exact (conLQ_layer con r).2

end WaveTurbulence.ZpSurj
