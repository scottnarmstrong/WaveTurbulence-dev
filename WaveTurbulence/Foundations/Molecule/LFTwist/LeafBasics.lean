/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CorePlacements
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # Actual leaf sets and parent layers for the LF-twist proof -/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} {G : Garden w}

/-- An actual leaf can only be an ancestor of itself among actual leaves. -/
theorem leaf_desc_iff (l m : GLeaf G.tree) : l.toNode.IsDesc m.toNode ↔ l = m := by
  constructor
  · intro h
    exact Subtype.ext (Prod.ext h.1 (leaf_prefix_eq l.2 (h.1 ▸ m.2) h.2))
  · intro h
    subst m
    exact ⟨rfl,List.prefix_refl _⟩

/-- The leaf set below an actual leaf is its singleton. -/
theorem leavesBelow_leaf (l : GLeaf G.tree) : l.toNode.leavesBelow = {l} := by
  ext m
  simp only [GNode.leavesBelow,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  exact (leaf_desc_iff l m).trans eq_comm

/-- Distinct actual leaves are incomparable. -/
theorem leaves_incomparable {l m : GLeaf G.tree} (hne : l ≠ m) : l.toNode.Incomparable m.toNode :=
  ⟨fun h => hne ((leaf_desc_iff l m).mp h),fun h => hne ((leaf_desc_iff m l).mp h).symm⟩

/-- An actual unmarked pair is completely paired as a union of its singleton subtrees. -/
theorem retained_pair_closed (P : CorePlacement G) :
    G.CompletelyPaired (P.retained.toNode.leavesBelow ∪ (G.pair P.retained).toNode.leavesBelow) := by
  have hn : G.pair P.retained ≠ P.retained := fun h => ((G.pair_eq_iff P.retained).mp h) P.unmarked
  rw [leavesBelow_leaf,leavesBelow_leaf]
  intro l hl
  rcases Finset.mem_union.mp hl with hl | hl
  · have he := Finset.mem_singleton.mp hl
    subst l
    exact ⟨hn,Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  · have he := Finset.mem_singleton.mp hl
    subst l
    rw [G.pair_pair]
    exact ⟨Ne.symm hn,Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩

/-- At a nonroot, the parent-layer definition is the actual parent branching-node layer. -/
theorem parentLayer_nonroot (LG : LayeredGarden w) (p : ℕ) (n : GNode LG.garden.tree) (hn : n.1.2 ≠ []) :
    LG.parentLayer p n = LG.layer (GNode.parent n hn).toNode := by
  simp only [LayeredGarden.parentLayer,hn,ite_false]
  rfl

/-- Incomparable node subtrees have disjoint actual leaf sets. -/
theorem leavesBelow_disjoint {a b : GNode G.tree} (hi : a.Incomparable b) :
    Disjoint a.leavesBelow b.leavesBelow := by
  apply Finset.disjoint_left.mpr
  intro l ha hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  by_cases hlen : a.1.2.length ≤ b.1.2.length
  · exact hi.1 ⟨ha'.1.trans hb'.1.symm,List.prefix_of_prefix_length_le ha'.2 hb'.2 hlen⟩
  · exact hi.2 ⟨hb'.1.trans ha'.1.symm,List.prefix_of_prefix_length_le hb'.2 ha'.2 (Nat.le_of_not_ge hlen)⟩

end WaveTurbulence.LFTwist
