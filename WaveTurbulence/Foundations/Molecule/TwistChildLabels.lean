/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistNodeLabels

/-! # Transport of actual child labels under the unit twist

TARGET twistexplain (d): the three exceptional node positions exchange
values, so every other branching node retains all three ordered child
values. The lower branch switches its two free child values.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Ordinary child nodes follow the actual parent transport and free-child permutation. -/
theorem naiveNodeEquiv_child {p : GBranch G.tree} {n : GNode G.tree} {i : Fin 3}
    (hc : n = p.child i) (hn : n ≠ P.lower.toNode) (hl : n ≠ (G.pair P.retained).toNode) :
    naiveNodeEquiv G P n = (coreBranchEquiv G P p).child (exchangeChildSlot P.lower.1 P.keep p.1 i) := by
  obtain ⟨q,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change b.toNode = p.child i at hc
    rw [show (nodePieceEquiv G.tree) (.inl b) = b.toNode from rfl,naiveNodeEquiv_branch]
    exact branch_child_transport G P hc (fun he => hn (congrArg GBranch.toNode he))
  | inr l =>
    change l.toNode = p.child i at hc
    rw [show (nodePieceEquiv G.tree) (.inr l) = l.toNode from rfl,naiveNodeEquiv_leaf]
    exact leaf_child_transport G P hc (fun he => hl (congrArg GLeaf.toNode he))

/-- An ordered child cannot equal its branching parent. -/
theorem child_ne_parent (p : GBranch G.tree) (i : Fin 3) : p.child i ≠ p.toNode := by
  intro he
  have hh := congrArg (fun n : GNode G.tree => n.1.2.length) he
  dsimp [GBranch.child,GBranch.toNode] at hh
  simp only [List.length_append,List.length_singleton] at hh
  omega

/-- Both transported leaves of the exceptional pair receive the old lower value. -/
theorem twistNodeLabels_paired {E : Type*} (κ : GNode G.tree → E) :
    twistNodeLabels G P κ (coreLeafEquiv G P (G.pair P.retained)).toNode = κ P.lower.toNode := by
  rw [twistNodeLabels_leaf]
  simp

/-- Every ordinary branching node retains its three ordered child values. -/
theorem twistNodeLabels_other_child {E : Type*} (κ : GNode G.tree → E)
    (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode)
    (p : GBranch G.tree) (hp : p ≠ P.lower) (i : Fin 3) :
    twistNodeLabels G P κ ((coreBranchEquiv G P p).child i) = κ (p.child i) := by
  by_cases hlow : p.child i = P.lower.toNode
  · have hparent : GNode.parent P.lower.toNode P.nonroot = p := parent_eq_of_child _ hlow.symm
    have hout : ¬ P.lower.toNode.IsDesc p.toNode := hparent ▸ lower_parent_outside G P
    have hn : (coreLeafEquiv G P (G.pair P.retained)).toNode = (coreBranchEquiv G P p).child i := by
      apply Subtype.ext
      change (coreLeafEquiv G P (G.pair P.retained)).1 =
        ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [i])
      rw [coreLeafEquiv_paired_val,coreBranchEquiv_fixed_val G P p hout]
      exact (congrArg (fun n : GNode G.tree => n.1) hlow).symm
    rw [← hn,twistNodeLabels_paired,hlow]
  · by_cases hpaired : p.child i = (G.pair P.retained).toNode
    · have hparent : GNode.parent (G.pair P.retained).toNode P.paired_nonroot = p :=
        parent_eq_of_child _ hpaired.symm
      have hout : ¬ P.lower.toNode.IsDesc p.toNode := hparent ▸ paired_parent_outside G P
      have hn : (coreBranchEquiv G P P.lower).toNode = (coreBranchEquiv G P p).child i := by
        apply Subtype.ext
        change (coreBranchEquiv G P P.lower).1 =
          ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [i])
        rw [coreBranchEquiv_lower_val,coreBranchEquiv_fixed_val G P p hout]
        exact (congrArg (fun n : GNode G.tree => n.1) hpaired).symm
      rw [← hn,twistNodeLabels_lower,hpaired]
      exact hpair
    · have hret : p.child i ≠ P.retained.toNode := by
        intro he
        have hparent : GNode.parent P.retained.toNode (retained_nonroot G P) = p :=
          parent_eq_of_child _ he.symm
        rw [retained_parent] at hparent
        exact hp hparent.symm
      have hn := naiveNodeEquiv_child G P (p := p) rfl hlow hpaired
      have hpv : p.1 ≠ P.lower.1 := fun he => hp (Subtype.ext he)
      simp only [exchangeChildSlot,hpv,ite_false] at hn
      rw [← hn,twistNodeLabels_naive]
      simp [switchedOldLabels,hlow,hret,hpaired]

/-- At the lower branch the transported child index is the free-child permutation. -/
theorem lower_naive_child (i : Fin 3) :
    naiveNodeEquiv G P (P.lower.child i) = (coreBranchEquiv G P P.lower).child (freeSwap P.keep i) := by
  have hn := child_ne_parent G P.lower i
  have hl : P.lower.child i ≠ (G.pair P.retained).toNode := by
    intro he
    apply P.paired_outside
    rw [← he]
    exact ⟨rfl,[i],rfl⟩
  simpa only [exchangeChildSlot,ite_true] using naiveNodeEquiv_child G P rfl hn hl

end WaveTurbulence.Twist
