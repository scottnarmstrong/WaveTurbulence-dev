/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftData
public import WaveTurbulence.Foundations.XChain.TopNodeEmbedding
public import WaveTurbulence.Foundations.XChain.LowerLeavesBelow
public import WaveTurbulence.Foundations.XChain.RootImageLeafSets
/-! Literal source root sets and leaf sets of the attached blocks. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def topLeafNodeEmbedding {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    GLeaf top ↪ GNode (graftForest top (blockGraftTrees top P low)) where
  toFun a := topNodeEmbedding top P low a.toNode
  inj' _ _ he := Subtype.ext (congrArg
    (fun a : GNode (graftForest top (blockGraftTrees top P low)) => a.1) he)

noncomputable def lowerRootNodeEmbedding {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) : Fin B.1.card ↪ GNode (graftForest top (blockGraftTrees top P low)) where
  toFun k := lowerNodeEmbedding top P low B (GNode.root (low B).tree k)
  inj' _ _ he := congrArg (fun a : GNode (low B).tree => a.1.1)
    ((lowerNodeEmbedding top P low B).injective he)

theorem lowerRootNodeEmbedding_eq {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (k : Fin B.1.card) :
    lowerRootNodeEmbedding top P low B k = topLeafNodeEmbedding top P low (B.1.equivFin.symm k).1 := by
  have he := topNodeEmbedding_lower_root top P low B k
  have hi := congrArg (fun a : GLeaf top => topNodeEmbedding top P low a.toNode)
    (blockRootEquiv_symm_eq top P B k)
  exact he.symm.trans hi

theorem lowerRootNodeEmbedding_univ {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) : univ.map (lowerRootNodeEmbedding top P low B) = B.1.map (topLeafNodeEmbedding top P low) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hu
    exact Finset.mem_map.mpr ⟨(B.1.equivFin.symm k).1, (B.1.equivFin.symm k).2,
      (lowerRootNodeEmbedding_eq top P low B k).symm⟩
  · intro hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    refine Finset.mem_map.mpr ⟨B.1.equivFin ⟨a, ha⟩, mem_univ _, ?_⟩
    exact (lowerRootNodeEmbedding_eq top P low B _).trans
      (congrArg (fun a : ↥B.1 => topLeafNodeEmbedding top P low a.1) (B.1.equivFin.symm_apply_apply ⟨a, ha⟩))

theorem graft_lower_rootImage_leaves {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) (K : Finset (Fin B.1.card)) :
    C.graft.leavesBelowSet (K.map (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)) =
      ((C.low B).garden.leavesOf K).map (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B) := by
  have he := leavesBelowSet_biUnion C.graft
    (K.map (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B))
  have hm := biUnion_map_congr
    (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B) GNode.leavesBelow
    (fun k => (GNode.root (C.low B).garden.tree k).leavesBelow)
    (fun k => lower_leavesBelow_eq_map C.top C.partition (fun B => (C.low B).garden) B
      (GNode.root (C.low B).garden.tree k)) K
  exact he.trans (hm.trans (congrArg
    (Finset.map (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B))
    (leavesOf_biUnion_roots (C.low B).garden K).symm))

end WaveTurbulence.Induct
