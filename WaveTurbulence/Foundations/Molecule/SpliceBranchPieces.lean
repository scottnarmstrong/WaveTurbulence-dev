/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceLeafPieces
public import WaveTurbulence.Foundations.Molecule.SpliceBranchSets
import Mathlib.Tactic

/-! # Concrete branching-node transport for three retained boundary subtrees
TARGET `block_clcn` (2). The common piece carrier consists of outside
branching nodes and branching nodes in each of the three actual boundary subtrees.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

variable {G} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

/-- The actual old branching nodes outside the replaced upper subtree. -/
abbrev SpliceOutsideBranch := {l : GBranch G.tree // ¬ a.toNode.IsDesc l.toNode}

/-- Disjoint branching-node pieces used on both sides of the surgery. -/
abbrev SpliceBranchPiece := SpliceOutsideBranch (G := G) (a := a) ⊕
  (Σ i : Fin 3, ↥(spliceNodeSubtree G (B.node i)).branching)

/-- Insert the pieces into the actual branching-node set of the spliced forest. -/
@[expose] def spliceBranchPieceNew : SpliceBranchPiece B → GBranch (spliceForest G a B.node)
  | .inl l => ⟨l.1.1,by
      by_cases hi : l.1.1.1 = a.1.1
      · change l.1.1.2 ∈ (spliceForest G a B.node l.1.1.1).branching
        rw [hi,spliceForest_branching]
        apply mem_union_left
        exact mem_filter.mpr ⟨hi ▸ l.1.2,fun hp => l.2 ⟨hi.symm,hp⟩⟩
      · rw [spliceForest_other G a B.node _ hi]
        exact l.1.2⟩
  | .inr ⟨i,q⟩ => ⟨(a.1.1,a.1.2++i::q.1),by
      rw [spliceForest_branching]
      apply mem_union_right
      apply mem_image.mpr
      exact ⟨i::q.1,(spliceCrown_child_branch G B.node i q.1).mpr q.2,rfl⟩⟩

/-- Insert the same pieces into the actual old branching-node set. -/
@[expose] def spliceBranchPieceOld : SpliceBranchPiece B → GBranch G.tree
  | .inl l => l.1
  | .inr ⟨i,q⟩ => ⟨((B.node i).1.1,(B.node i).1.2++q.1),by
      exact (Comb.subtree_branching_iff (spliceNodeSubtree_spec G (B.node i)) q.1).mp q.2⟩

theorem spliceBranchPieceNew_injective : Function.Injective (spliceBranchPieceNew B) := by
  rintro (l | ⟨i,q⟩) (m | ⟨j,r⟩) he
  · have hval : l.1.1 = m.1.1 := congrArg (fun n : GBranch (spliceForest G a B.node) => n.1) he
    have hlm : l.1 = m.1 := Subtype.ext hval
    exact congrArg Sum.inl (Subtype.ext hlm)
  · have hi : a.toNode.IsDesc l.1.toNode := by
      have hidx : l.1.1.1 = a.1.1 := congrArg (fun n : GBranch (spliceForest G a B.node) => n.1.1) he
      have hp : l.1.1.2 = a.1.2++j::r.1 := congrArg (fun n : GBranch (spliceForest G a B.node) => n.1.2) he
      exact ⟨hidx.symm,⟨j::r.1,hp.symm⟩⟩
    exact (l.2 hi).elim
  · have hi : a.toNode.IsDesc m.1.toNode := by
      have hidx : a.1.1 = m.1.1.1 := congrArg (fun n : GBranch (spliceForest G a B.node) => n.1.1) he
      have hp : a.1.2++i::q.1 = m.1.1.2 := congrArg (fun n : GBranch (spliceForest G a B.node) => n.1.2) he
      exact ⟨hidx,⟨i::q.1,hp⟩⟩
    exact (m.2 hi).elim
  · have hp : a.1.2++i::q.1 = a.1.2++j::r.1 := congrArg (fun l => l.1.2) he
    have h := List.cons.inj (List.append_cancel_left hp)
    rcases h with ⟨rfl,hh⟩
    have hqr : q = r := Subtype.ext hh
    subst r
    rfl

/-- An old branching-node survives precisely when it is outside, or below a retained root. -/
@[expose] def IsSpliceRetainedBranch (l : GBranch G.tree) : Prop :=
  ¬ a.toNode.IsDesc l.toNode ∨ ∃ i, (B.node i).IsDesc l.toNode

theorem spliceBranchPieceOld_retained (p : SpliceBranchPiece B) : IsSpliceRetainedBranch B (spliceBranchPieceOld B p) := by
  cases p with
  | inl l => exact Or.inl l.2
  | inr p => exact Or.inr ⟨p.1,rfl,⟨p.2.1,rfl⟩⟩

end WaveTurbulence.Mole
