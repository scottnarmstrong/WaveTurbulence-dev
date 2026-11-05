/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsedCouplePairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LabelledGraph

/-! # Actual surviving branch embeddings and inherited labels after source collapse -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem collapseNodeForest_branch_iff {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) (x : Address w) :
    x.2 ∈ (Comb.collapseNodeForest tree a x.1).branching ↔
      x.2 ∈ (tree x.1).branching ∧ ¬ Below a.1 x := by
  change x.2 ∈ (Comb.replaceNodeForest tree a .leaf x.1).branching ↔ _
  rw [replaceNodeForest_branch_iff]
  simp only [TTree.branching,Finset.notMem_empty,false_and,exists_false,or_false]

theorem collapsePairForest_branch_iff {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (x : Address w) :
    x.2 ∈ (collapsePairForest tree a b hab x.1).branching ↔
      x.2 ∈ (tree x.1).branching ∧ ¬ Below a.1 x ∧ ¬ Below b.1 x := by
  change x.2 ∈ (Comb.collapseNodeForest (Comb.collapseNodeForest tree a)
    (Comb.collapseOtherNode tree a b hab) x.1).branching ↔ _
  rw [collapseNodeForest_branch_iff,collapseNodeForest_branch_iff]
  change (_ ∧ _) ∧ ¬ Below b.1 x ↔ _
  exact and_assoc

/-- Surviving source branches retain exactly their old addresses under couple collapse. -/
def collapseCoupleBranchEmbedding {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) : GBranch (collapseCoupleGarden h).tree ↪ GBranch G.tree where
  toFun x := ⟨x.1,((collapsePairForest_branch_iff G.tree a b (Comb.subCouple_incomparable h) x.1).mp x.2).1⟩
  inj' := fun _x _y he => Subtype.ext (congrArg (fun z : GBranch G.tree => z.1) he)

/-- Surviving source branches of a paired-tree collapse use the exact inserted-prefix embedding. -/
noncomputable def collapsePairedTreeBranchEmbedding {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) : GBranch (collapsePairedTreeGarden h).tree ↪ GBranch G.tree :=
  replacementBranchEmbedding G.tree a b (Comb.collapseDataOfDesc h.1).path (collapseData_frame h.1)

namespace LabelledGarden

/-- Actual couple collapse with inherited original branch labels. -/
noncomputable def collapseCouple {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) : LabelledGarden w B :=
  ⟨collapseCoupleGarden h,(collapseCoupleBranchEmbedding h).trans G.label⟩

/-- Actual paired-tree collapse with inherited original branch labels. -/
noncomputable def collapsePairedTree {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubPairedTree G.garden a b) : LabelledGarden w B :=
  ⟨collapsePairedTreeGarden h,(collapsePairedTreeBranchEmbedding h).trans G.label⟩

end LabelledGarden
end WaveTurbulence.Reg.Skeleton
