/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementForest
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairing

/-! # Exact leaf and branch embeddings when a rooted interval is collapsed

Replace an upper subtree by the subtree at its actual descendant. Prefix
insertion embeds the resulting leaves/branches back into the original forest.
Its image is exactly the complement of the removed upper-minus-lower region.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Actual descendant positions have a literal relative path. -/
theorem descendant_exists_frame {w : ℕ} {tree : Fin w → TTree} (a b : GNode tree) (h : a.IsDesc b) :
    ∃ p : Path, b.1 = addrExt a.1 p := by
  obtain ⟨p,hp⟩ := h.2
  exact ⟨p,Prod.ext h.1.symm hp.symm⟩

/-- Every transported new leaf is an actual original leaf. -/
theorem replacement_stretch_leaf {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) (x : Address w)
    (hx : x.2 ∈ (Comb.replaceNodeForest tree a (Comb.nodeSubtree b) x.1).leaves) :
    (stretch a.1 p x).2 ∈ (tree (stretch a.1 p x).1).leaves := by
  rcases (replaceNodeForest_leaf_iff tree a (Comb.nodeSubtree b) x).mp hx with ⟨hl,ha⟩ | ⟨r,hr,he⟩
  · rw [stretch_outside a.1 p x ha]
    exact hl
  · rw [he,stretch_frame,← addrExt_append,← hp]
    exact (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec b) r).mp hr

/-- The surviving original leafs are precisely those outside the upper root or below the lower root. -/
theorem replacement_leaf_image {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) (y : GLeaf tree) :
    (¬ Below a.1 y.1 ∨ Below b.1 y.1) ↔
      ∃ x : GLeaf (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)), stretch a.1 p x.1 = y.1 := by
  constructor
  · rintro (ha | hb)
    · let x : GLeaf (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) :=
        ⟨y.1,(replaceNodeForest_leaf_iff tree a (Comb.nodeSubtree b) _).mpr (Or.inl ⟨y.2,ha⟩)⟩
      exact ⟨x,stretch_outside a.1 p y.1 ha⟩
    · obtain ⟨r,hr⟩ := below_exists_frame b.1 y.1 hb
      have hy : r ∈ (Comb.nodeSubtree b).leaves := by
        apply (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec b) r).mpr
        change (addrExt b.1 r).2 ∈ (tree (addrExt b.1 r).1).leaves
        rw [← hr]
        exact y.2
      let x : GLeaf (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) :=
        ⟨addrExt a.1 r,(replaceNodeForest_leaf_iff tree a (Comb.nodeSubtree b) _).mpr (Or.inr ⟨r,hy,rfl⟩)⟩
      refine ⟨x,?_⟩
      change stretch a.1 p (addrExt a.1 r) = y.1
      rw [stretch_frame,← addrExt_append,← hp]
      exact hr.symm
  · rintro ⟨x,hx⟩
    rcases (replaceNodeForest_leaf_iff tree a (Comb.nodeSubtree b) x.1).mp x.2 with ⟨hl,ha⟩ | ⟨r,hr,he⟩
    · rw [stretch_outside a.1 p x.1 ha] at hx
      exact Or.inl (by rw [← hx]; exact ha)
    · rw [he,stretch_frame,← addrExt_append,← hp] at hx
      exact Or.inr (by rw [← hx]; exact below_extend b.1 r)

/-- The exact leaf embedding induced by collapsing this actual rooted interval. -/
def replacementLeafEmbedding {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) : GLeaf (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) ↪ GLeaf tree where
  toFun x := ⟨stretch a.1 p x.1,replacement_stretch_leaf tree a b p hp x.1 x.2⟩
  inj' := by
    intro x y he
    apply Subtype.ext
    exact stretch_injective a.1 p (congrArg (fun z : GLeaf tree => z.1) he)

/-- Every transported new branch is an actual original branch. -/
theorem replacement_stretch_branch {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) (x : Address w)
    (hx : x.2 ∈ (Comb.replaceNodeForest tree a (Comb.nodeSubtree b) x.1).branching) :
    (stretch a.1 p x).2 ∈ (tree (stretch a.1 p x).1).branching := by
  rcases (replaceNodeForest_branch_iff tree a (Comb.nodeSubtree b) x).mp hx with ⟨hl,ha⟩ | ⟨r,hr,he⟩
  · rw [stretch_outside a.1 p x ha]
    exact hl
  · rw [he,stretch_frame,← addrExt_append,← hp]
    exact (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b) r).mp hr

/-- The surviving original branchs are precisely those outside the upper root or below the lower root. -/
theorem replacement_branch_image {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) (y : GBranch tree) :
    (¬ Below a.1 y.1 ∨ Below b.1 y.1) ↔
      ∃ x : GBranch (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)), stretch a.1 p x.1 = y.1 := by
  constructor
  · rintro (ha | hb)
    · let x : GBranch (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) :=
        ⟨y.1,(replaceNodeForest_branch_iff tree a (Comb.nodeSubtree b) _).mpr (Or.inl ⟨y.2,ha⟩)⟩
      exact ⟨x,stretch_outside a.1 p y.1 ha⟩
    · obtain ⟨r,hr⟩ := below_exists_frame b.1 y.1 hb
      have hy : r ∈ (Comb.nodeSubtree b).branching := by
        apply (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b) r).mpr
        change (addrExt b.1 r).2 ∈ (tree (addrExt b.1 r).1).branching
        rw [← hr]
        exact y.2
      let x : GBranch (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) :=
        ⟨addrExt a.1 r,(replaceNodeForest_branch_iff tree a (Comb.nodeSubtree b) _).mpr (Or.inr ⟨r,hy,rfl⟩)⟩
      refine ⟨x,?_⟩
      change stretch a.1 p (addrExt a.1 r) = y.1
      rw [stretch_frame,← addrExt_append,← hp]
      exact hr.symm
  · rintro ⟨x,hx⟩
    rcases (replaceNodeForest_branch_iff tree a (Comb.nodeSubtree b) x.1).mp x.2 with ⟨hl,ha⟩ | ⟨r,hr,he⟩
    · rw [stretch_outside a.1 p x.1 ha] at hx
      exact Or.inl (by rw [← hx]; exact ha)
    · rw [he,stretch_frame,← addrExt_append,← hp] at hx
      exact Or.inr (by rw [← hx]; exact below_extend b.1 r)

/-- The exact branch embedding induced by collapsing this actual rooted interval. -/
def replacementBranchEmbedding {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (p : Path)
    (hp : b.1 = addrExt a.1 p) : GBranch (Comb.replaceNodeForest tree a (Comb.nodeSubtree b)) ↪ GBranch tree where
  toFun x := ⟨stretch a.1 p x.1,replacement_stretch_branch tree a b p hp x.1 x.2⟩
  inj' := by
    intro x y he
    apply Subtype.ext
    exact stretch_injective a.1 p (congrArg (fun z : GBranch tree => z.1) he)

end WaveTurbulence.Reg.Skeleton
