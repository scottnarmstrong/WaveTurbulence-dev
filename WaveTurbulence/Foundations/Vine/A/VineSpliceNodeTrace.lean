/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceOuterSlot
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceNodes
/-! The literal old node names and retained-parent ports of the actual fold. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- Combine the actual old branch and leaf names into old node names. -/
noncomputable def spliceOldNode (l : List (CLBlock G)) (n : GNode (spliceFold G l).G.tree) :
    GNode G.tree :=
  match (nodePieceEquiv (spliceFold G l).G.tree).symm n with
  | .inl b => ((spliceFold G l).M.ob b).toNode
  | .inr q => ((spliceFoldLeafTrace l).leaf q).toNode

theorem spliceOldNode_branch (l : List (CLBlock G)) (b : GBranch (spliceFold G l).G.tree) :
    spliceOldNode l b.toNode = ((spliceFold G l).M.ob b).toNode := by
  unfold spliceOldNode
  change (match (nodePieceEquiv _).symm ((nodePieceEquiv _) (.inl b)) with
    | .inl b => _ | .inr q => _) = _
  rw [Equiv.symm_apply_apply]

theorem spliceOldNode_leaf (l : List (CLBlock G)) (q : GLeaf (spliceFold G l).G.tree) :
    spliceOldNode l q.toNode = ((spliceFoldLeafTrace l).leaf q).toNode := by
  unfold spliceOldNode
  change (match (nodePieceEquiv _).symm ((nodePieceEquiv _) (.inr q)) with
    | .inl b => _ | .inr q => _) = _
  rw [Equiv.symm_apply_apply]

/-- Actual old names preserve the root predicate. -/
theorem spliceOldNode_root (l : List (CLBlock G)) (n : GNode (spliceFold G l).G.tree) :
    (spliceOldNode l n).1.2 = [] ↔ n.1.2 = [] := by
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (spliceFold G l).G.tree).surjective n
  cases p with
  | inl b =>
    change (spliceOldNode l b.toNode).1.2 = [] ↔ _
    rw [spliceOldNode_branch]
    exact (spliceFold G l).M.ob_root b
  | inr q =>
    change (spliceOldNode l q.toNode).1.2 = [] ↔ _
    rw [spliceOldNode_leaf]
    exact (spliceFoldLeafTrace l).root q

/-- Actual old node parents contract by the fold's actual class function. -/
theorem spliceOldNode_parent (l : List (CLBlock G)) (n : GNode (spliceFold G l).G.tree)
    (hn : n.1.2 ≠ []) (ho : (spliceOldNode l n).1.2 ≠ []) :
    (spliceFold G l).M.ob (GNode.parent n hn) =
      repC (spliceFold G l).cls (GNode.parent (spliceOldNode l n) ho) := by
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (spliceFold G l).G.tree).surjective n
  cases p with
  | inl b =>
    change (spliceOldNode l b.toNode).1.2 ≠ [] at ho
    change _ = repC _ (GNode.parent (spliceOldNode l b.toNode) ho)
    simp only [spliceOldNode_branch] at ho ⊢
    exact (spliceFold G l).M.ob_parent b hn ho
  | inr q =>
    change (spliceOldNode l q.toNode).1.2 ≠ [] at ho
    change _ = repC _ (GNode.parent (spliceOldNode l q.toNode) ho)
    simp only [spliceOldNode_leaf] at ho ⊢
    exact (spliceFoldLeafTrace l).parent q hn ho

/-- The actual old node port is unchanged when its original parent is retained. -/
theorem spliceOldNode_port (l : List (CLBlock G)) (n : GNode (spliceFold G l).G.tree)
    (hn : n.1.2 ≠ []) (ho : (spliceOldNode l n).1.2 ≠ [])
    (hp : repC (spliceFold G l).cls (GNode.parent (spliceOldNode l n) ho) =
      GNode.parent (spliceOldNode l n) ho) :
    n.1.2.getLast hn = (spliceOldNode l n).1.2.getLast ho := by
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (spliceFold G l).G.tree).surjective n
  cases p with
  | inl b =>
    change (spliceOldNode l b.toNode).1.2 ≠ [] at ho
    change repC _ (GNode.parent (spliceOldNode l b.toNode) ho) = GNode.parent (spliceOldNode l b.toNode) ho at hp
    change _ = (spliceOldNode l b.toNode).1.2.getLast ho
    simp only [spliceOldNode_branch] at ho hp ⊢
    exact (spliceFoldPortTrace l).branch b hn ho hp
  | inr q =>
    change (spliceOldNode l q.toNode).1.2 ≠ [] at ho
    change repC _ (GNode.parent (spliceOldNode l q.toNode) ho) = GNode.parent (spliceOldNode l q.toNode) ho at hp
    change _ = (spliceOldNode l q.toNode).1.2.getLast ho
    simp only [spliceOldNode_leaf] at ho hp ⊢
    exact (spliceFoldPortTrace l).leaf q hn ho hp

/-- Every actual old branch is fixed by the fold retraction. -/
theorem splice_old_branch_fixed (st : SpState G) (b : GBranch st.G.tree) :
    repC st.cls (st.M.ob b) = st.M.ob b := by
  rcases (st.M.ob_range _).mp ⟨b, rfl⟩ with h | h <;> unfold repC <;> rw [h] <;> rfl

end WaveTurbulence.VineA
