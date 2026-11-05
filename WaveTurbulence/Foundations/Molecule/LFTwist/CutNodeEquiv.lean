/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ThresholdCriterion

/-! # The node correspondence preserving all threshold cuts

The old lower branch corresponds to the new outside partner leaf, and
the old outside partner leaf to the new lower branch. Every other node
follows its subtree. Unlike the naive correspondence, this map preserves
parent layers as well as node layers after the coherent collapse.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Swap the old lower and partner node roles before the actual node transport. -/
@[expose] noncomputable def cutNodeEquiv : GNode G.tree ≃ GNode (unitTwistGarden G P).tree :=
  (Equiv.swap P.lower.toNode (G.pair P.retained).toNode).trans (naiveNodeEquiv G P)

/-- The old lower branch becomes the new partner leaf at its original address. -/
theorem cutNodeEquiv_lower : cutNodeEquiv G P P.lower.toNode =
    (coreLeafEquiv G P (G.pair P.retained)).toNode := by
  change naiveNodeEquiv G P (Equiv.swap _ _ P.lower.toNode) = _
  rw [Equiv.swap_apply_left,naiveNodeEquiv_leaf]

/-- The old partner leaf becomes the new lower branch at its original address. -/
theorem cutNodeEquiv_paired : cutNodeEquiv G P (G.pair P.retained).toNode =
    (coreBranchEquiv G P P.lower).toNode := by
  change naiveNodeEquiv G P (Equiv.swap _ _ (G.pair P.retained).toNode) = _
  rw [Equiv.swap_apply_right,naiveNodeEquiv_branch]

/-- Every other node follows the actual naive subtree transport. -/
theorem cutNodeEquiv_other (n : GNode G.tree) (hb : n ≠ P.lower.toNode)
    (hp : n ≠ (G.pair P.retained).toNode) : cutNodeEquiv G P n = naiveNodeEquiv G P n := by
  exact congrArg (naiveNodeEquiv G P) (Equiv.swap_apply_of_ne_of_ne hb hp)

/-- Parent branching-node proofs are irrelevant to actual equality of node addresses. -/
theorem nodeParent_congr {F : Fin w → TTree} {n m : GNode F} (hn : n.1.2 ≠ []) (hm : m.1.2 ≠ [])
    (he : n = m) : GNode.parent n hn = GNode.parent m hm := by
  apply Subtype.ext
  exact congrArg (fun q : GNode F => (q.1.1,q.1.2.dropLast)) he

/-- The naive node bijection preserves the distinction between roots and nonroots. -/
theorem naiveNodeEquiv_nonroot (n : GNode G.tree) : (naiveNodeEquiv G P n).1.2 ≠ [] ↔ n.1.2 ≠ [] := by
  obtain ⟨x,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases x with
  | inl b =>
    have hv := congrArg (fun n : GNode (unitTwistGarden G P).tree => n.1.2) (naiveNodeEquiv_branch G P b)
    exact hv.symm ▸ coreBranchEquiv_nonroot G P b
  | inr l =>
    have hv := congrArg (fun n : GNode (unitTwistGarden G P).tree => n.1.2) (naiveNodeEquiv_leaf G P l)
    exact hv.symm ▸ coreLeafEquiv_nonroot G P l

/-- Ordinary parent branching nodes follow the actual branch bijection. -/
theorem naiveNodeEquiv_parent (n : GNode G.tree) (hn : n.1.2 ≠ [])
    (hb : n ≠ P.lower.toNode) (hp : n ≠ (G.pair P.retained).toNode) :
    GNode.parent (naiveNodeEquiv G P n) ((naiveNodeEquiv_nonroot G P n).mpr hn) =
      coreBranchEquiv G P (GNode.parent n hn) := by
  obtain ⟨x,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases x with
  | inl b =>
    have hne : b ≠ P.lower := fun he => hb (congrArg GBranch.toNode he)
    exact (nodeParent_congr _ _ (naiveNodeEquiv_branch G P b)).trans (branchParent_transport G P b hn hne)
  | inr l =>
    have hne : l ≠ G.pair P.retained := fun he => hp (congrArg GLeaf.toNode he)
    exact (nodeParent_congr _ _ (naiveNodeEquiv_leaf G P l)).trans (leafParent_transport G P l hn hne)

/-- The new outside partner retains the old lower branch's original parent. -/
theorem newPaired_parent :
    GNode.parent (coreLeafEquiv G P (G.pair P.retained)).toNode
        ((coreLeafEquiv_nonroot G P (G.pair P.retained)).mpr P.paired_nonroot) =
      coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot) := by
  apply Subtype.ext
  change ((coreLeafEquiv G P (G.pair P.retained)).1.1,
    (coreLeafEquiv G P (G.pair P.retained)).1.2.dropLast) = _
  rw [coreLeafEquiv_paired_val,coreBranchEquiv_fixed_val G P _ (lower_parent_outside G P)]
  rfl

variable (LG : LayeredGarden w) (R : CorePlacement LG.garden)

/-- The cut-node map preserves the actual layer of every node. -/
theorem cutNodeEquiv_layer (he : SameLowerLayer LG R) (n : GNode LG.garden.tree) :
    (unitLayerTwist LG R he).layer (cutNodeEquiv LG.garden R n) = LG.layer n := by
  by_cases hb : n = R.lower.toNode
  · subst n
    exact (congrArg (unitLayerTwist LG R he).layer (cutNodeEquiv_lower LG.garden R)).trans
      ((unitLayerTwist_leaf LG R he _).trans ((LG.isLayering.2 R.retained).symm.trans he.symm))
  · by_cases hp : n = (LG.garden.pair R.retained).toNode
    · subst n
      exact (congrArg (unitLayerTwist LG R he).layer (cutNodeEquiv_paired LG.garden R)).trans
        ((unitLayerTwist_branch LG R he _).trans (he.trans (LG.isLayering.2 R.retained)))
    · exact (congrArg (unitLayerTwist LG R he).layer (cutNodeEquiv_other LG.garden R n hb hp)).trans
        (unitLayerTwist_node LG R he n)

/-- Ordinary naive images preserve parent layers, including root convention p. -/
theorem naiveNodeEquiv_parentLayer (he : SameLowerLayer LG R) (p : ℕ) (n : GNode LG.garden.tree)
    (hb : n ≠ R.lower.toNode) (hp : n ≠ (LG.garden.pair R.retained).toNode) :
    (unitLayerTwist LG R he).parentLayer p (naiveNodeEquiv LG.garden R n) = LG.parentLayer p n := by
  by_cases hn : n.1.2 = []
  · have hn' : (naiveNodeEquiv LG.garden R n).1.2 = [] := by
      by_contra hh
      exact ((naiveNodeEquiv_nonroot LG.garden R n).mp hh) hn
    simp only [LayeredGarden.parentLayer,hn,hn',ite_true]
  · have hn' := (naiveNodeEquiv_nonroot LG.garden R n).mpr hn
    exact (parentLayer_nonroot (unitLayerTwist LG R he) p _ hn').trans
      ((congrArg (fun b : GBranch (unitTwistGarden LG.garden R).tree =>
        (unitLayerTwist LG R he).layer b.toNode) (naiveNodeEquiv_parent LG.garden R n hn hb hp)).trans
          ((unitLayerTwist_branch LG R he _).trans (parentLayer_nonroot LG p n hn).symm))

/-- The swapped-node correspondence preserves every parent layer, not only
those in one threshold range. This includes all source vine cases uniformly. -/
theorem cutNodeEquiv_parentLayer (he : SameLowerLayer LG R) (p : ℕ) (n : GNode LG.garden.tree) :
    (unitLayerTwist LG R he).parentLayer p (cutNodeEquiv LG.garden R n) = LG.parentLayer p n := by
  by_cases hb : n = R.lower.toNode
  · subst n
    have hn := (coreLeafEquiv_nonroot LG.garden R (LG.garden.pair R.retained)).mpr R.paired_nonroot
    exact (congrArg ((unitLayerTwist LG R he).parentLayer p) (cutNodeEquiv_lower LG.garden R)).trans
      ((parentLayer_nonroot (unitLayerTwist LG R he) p _ hn).trans
        ((congrArg (fun b : GBranch (unitTwistGarden LG.garden R).tree =>
          (unitLayerTwist LG R he).layer b.toNode) (newPaired_parent LG.garden R)).trans
            ((unitLayerTwist_branch LG R he _).trans (parentLayer_nonroot LG p _ R.nonroot).symm)))
  · by_cases hp : n = (LG.garden.pair R.retained).toNode
    · subst n
      have hn := (coreBranchEquiv_nonroot LG.garden R R.lower).mpr R.nonroot
      exact (congrArg ((unitLayerTwist LG R he).parentLayer p) (cutNodeEquiv_paired LG.garden R)).trans
        ((parentLayer_nonroot (unitLayerTwist LG R he) p _ hn).trans
          ((congrArg (fun b : GBranch (unitTwistGarden LG.garden R).tree =>
            (unitLayerTwist LG R he).layer b.toNode) (lower_new_parent LG.garden R)).trans
              ((unitLayerTwist_branch LG R he _).trans (parentLayer_nonroot LG p _ R.paired_nonroot).symm)))
    · exact (congrArg ((unitLayerTwist LG R he).parentLayer p) (cutNodeEquiv_other LG.garden R n hb hp)).trans
        (naiveNodeEquiv_parentLayer LG R he p n hb hp)

/-- Every integer threshold cut root corresponds exactly under the actual map. -/
theorem cutNodeEquiv_isCutRoot (he : SameLowerLayer LG R) (p r : ℕ) (n : GNode LG.garden.tree) :
    IsCutRoot (unitLayerTwist LG R he) p r (cutNodeEquiv LG.garden R n) ↔ IsCutRoot LG p r n := by
  unfold IsCutRoot
  rw [cutNodeEquiv_layer LG R he n,cutNodeEquiv_parentLayer LG R he p n]

end WaveTurbulence.LFTwist
