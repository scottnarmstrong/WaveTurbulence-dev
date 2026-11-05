/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseBranchLabels
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingStretchBoundary

/-! # Exact incoming slots for all nodes of an actual paired-tree collapse -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem replacement_stretch_node {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) (x : GNode (Comb.replaceNodeForest tree a (Comb.nodeSubtree b))) :
    (stretch a.1 p x.1).2 ∈ (tree (stretch a.1 p x.1).1).nodes := by
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp x.2 with hl | hb
  · exact (Comb.TreePath.mem_nodes_iff _ _).mpr
      (Or.inl (replacement_stretch_leaf tree a b p hp x.1 hl))
  · exact (Comb.TreePath.mem_nodes_iff _ _).mpr
      (Or.inr (replacement_stretch_branch tree a b p hp x.1 hb))

/-- Every actual node maps by exactly the same inserted prefix as branches and leaves. -/
noncomputable def collapsePairedTreeNodeEmbedding {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) : GNode (collapsePairedTreeGarden h).tree ↪ GNode G.tree where
  toFun x := ⟨stretch a.1 (Comb.collapseDataOfDesc h.1).path x.1,
    replacement_stretch_node G.tree a b _ (collapseData_frame h.1) x⟩
  inj' := fun _x _y he => Subtype.ext
    (stretch_injective a.1 _ (congrArg (fun z : GNode G.tree => z.1) he))

namespace LabelledGarden

theorem collapsePairedTree_incoming_nonboundary {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubPairedTree G.garden a b)
    (x : GNode (collapsePairedTreeGarden h).tree) (hx : x.1 ≠ a.1) :
    (G.collapsePairedTree h).incoming x = G.incoming (collapsePairedTreeNodeEmbedding h x) := by
  exact (G.collapsePairedTree h).incoming_eq_of_stretch_embedding G a.1
    (Comb.collapseDataOfDesc h.1).path (collapsePairedTreeBranchEmbedding h)
    (fun _ => rfl) (fun _ => rfl) x _ rfl hx

theorem collapsePairedTree_incoming_boundary {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubPairedTree G.garden a b)
    (x : GNode (collapsePairedTreeGarden h).tree) (hx : x.1 = a.1) :
    (G.collapsePairedTree h).incoming x = G.incoming a := by
  exact (G.collapsePairedTree h).incoming_stretch_boundary G a (Comb.collapseDataOfDesc h.1).path
    (collapsePairedTreeBranchEmbedding h) (fun _ => rfl) (fun _ => rfl) x hx

end LabelledGarden
end WaveTurbulence.Reg.Skeleton
