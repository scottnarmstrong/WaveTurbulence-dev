/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceBranchPieces
import Mathlib.Tactic

/-! # All spliced branches except the retained crown are transported old branches -/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

/-- The single atom retained as the crown of the spliced subtree. -/
@[expose] def spliceCrownBranch : GBranch (spliceForest G a B.node) :=
  ⟨(a.1.1,a.1.2),by
    rw [spliceForest_branching]
    apply mem_union_right
    apply mem_image.mpr
    exact ⟨[],by simp [spliceCrown,TTree.branching],List.append_nil _⟩⟩

theorem spliceBranchPieceNew_ne_crown (p : SpliceBranchPiece B) :
    spliceBranchPieceNew B p ≠ spliceCrownBranch B := by
  intro he
  cases p with
  | inl l =>
    have hi : l.1.1.1 = a.1.1 := congrArg (fun c : GBranch (spliceForest G a B.node) => c.1.1) he
    have hp : l.1.1.2 = a.1.2 := congrArg (fun c : GBranch (spliceForest G a B.node) => c.1.2) he
    apply l.2
    refine ⟨hi.symm,?_⟩
    change a.1.2 <+: l.1.1.2
    exact ⟨[],by simpa only [List.append_nil] using hp.symm⟩
  | inr p =>
    have hp : a.1.2++p.1::p.2.1 = a.1.2 :=
      congrArg (fun c : GBranch (spliceForest G a B.node) => c.1.2) he
    have hl := congrArg List.length hp
    simp only [List.length_append,List.length_cons] at hl
    omega

theorem spliceBranchPieceNew_surjective_except_crown (c : GBranch (spliceForest G a B.node))
    (hc : c ≠ spliceCrownBranch B) : ∃ p : SpliceBranchPiece B, spliceBranchPieceNew B p = c := by
  by_cases hi : c.1.1 = a.1.1
  · have hl : c.1.2 ∈ (spliceForest G a B.node a.1.1).branching := hi ▸ c.2
    rw [spliceForest_branching] at hl
    rcases mem_union.mp hl with hout | hin
    · obtain ⟨hold,hn⟩ := mem_filter.mp hout
      let k : GBranch G.tree := ⟨c.1,hi.symm ▸ hold⟩
      have hk : ¬ a.toNode.IsDesc k.toNode := fun h => hn h.2
      exact ⟨.inl ⟨k,hk⟩,Subtype.ext rfl⟩
    · obtain ⟨p,hp,he⟩ := mem_image.mp hin
      cases p with
      | nil =>
        have hpath : c.1.2 = a.1.2 := by simpa only [List.append_nil] using he.symm
        exact (hc (Subtype.ext (Prod.ext hi hpath))).elim
      | cons i q =>
        have hq := (spliceCrown_child_branch G B.node i q).mp hp
        exact ⟨.inr ⟨i,⟨q,hq⟩⟩,Subtype.ext (Prod.ext hi.symm he)⟩
  · have hl : c.1.2 ∈ (G.tree c.1.1).branching := by
      have hm := c.2
      rw [spliceForest_other G a B.node _ hi] at hm
      exact hm
    let k : GBranch G.tree := ⟨c.1,hl⟩
    have hk : ¬ a.toNode.IsDesc k.toNode := fun h => hi h.1.symm
    exact ⟨.inl ⟨k,hk⟩,Subtype.ext rfl⟩

end WaveTurbulence.Mole
