/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistAddressChildren

/-! # Actual branching addresses under the uniform unit-twist map -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Actual branch transport is given by the same uniform address formula as leaf transport. -/
theorem coreBranchEquiv_address (b : GBranch G.tree) :
    (coreBranchEquiv G P b).1 = exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep b.1 := by
  obtain ⟨p,rfl⟩ := (coreBranchPiece G P).symm.surjective b
  rw [coreBranchEquiv_piece]
  cases p with
  | inl b =>
    have hout : ¬ (b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2) := by
      rintro ⟨hi,hp⟩
      exact leaf_not_prefix_branch (collapsedRoot G P.lower).2 (hi ▸ b.2) hp
    have hp : b.1 ≠ (G.pair P.retained).1 := by
      intro he
      have hn : b.toNode = (pairedHole G P).toNode := Subtype.ext he
      exact Mole.branch_toNode_ne_leaf b (pairedHole G P) hn
    change b.1 = exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep b.1
    simp [exchangeAddress,hout,hp]
  | inr q =>
    change ((pairedHole G P).1.1,(pairedHole G P).1.2 ++ switchPath P.keep q.1) =
      exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep (P.lower.1.1,P.lower.1.2 ++ q.1)
    simp [exchangeAddress]
    exact ⟨rfl,rfl⟩

/-- A parent-branch address never equals the paired leaf address. -/
theorem branch_ne_paired_address (b : GBranch G.tree) : b.1 ≠ (G.pair P.retained).1 := by
  intro he
  exact Mole.branch_toNode_ne_leaf b (G.pair P.retained) (Subtype.ext he)

/-- The actual branch image of every ordinary parent-child relation keeps its endpoints. -/
theorem branch_child_transport {p c : GBranch G.tree} {i : Fin 3}
    (hchild : c.toNode = p.child i) (hc : c ≠ P.lower) :
    (coreBranchEquiv G P c).toNode =
      (coreBranchEquiv G P p).child (exchangeChildSlot P.lower.1 P.keep p.1 i) := by
  apply Subtype.ext
  change (coreBranchEquiv G P c).1 =
    ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [_])
  rw [coreBranchEquiv_address,coreBranchEquiv_address]
  have hv : c.1 = (p.1.1,p.1.2 ++ [i]) := congrArg (fun n : GNode G.tree => n.1) hchild
  have hc₀ : (p.1.1,p.1.2 ++ [i]) ≠ P.lower.1 := fun he => hc (Subtype.ext (hv.trans he))
  have hc₁ : (p.1.1,p.1.2 ++ [i]) ≠ (G.pair P.retained).1 := by
    rw [← hv]
    exact branch_ne_paired_address G P c
  rw [hv]
  exact exchangeAddress_child _ _ _ _ _ (branch_ne_paired_address G P p) hc₀ hc₁

/-- Ordinary LP child positions are transported with their actual parent branch. -/
theorem leaf_child_transport {p : GBranch G.tree} {l : GLeaf G.tree} {i : Fin 3}
    (hchild : l.toNode = p.child i) (hl : l ≠ G.pair P.retained) :
    (coreLeafEquiv G P l).toNode =
      (coreBranchEquiv G P p).child (exchangeChildSlot P.lower.1 P.keep p.1 i) := by
  apply Subtype.ext
  change (coreLeafEquiv G P l).1 =
    ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [_])
  rw [coreLeafEquiv_address,coreBranchEquiv_address]
  have hv : l.1 = (p.1.1,p.1.2 ++ [i]) := congrArg (fun n : GNode G.tree => n.1) hchild
  have hc₀ : (p.1.1,p.1.2 ++ [i]) ≠ P.lower.1 := by
    intro he
    exact Mole.branch_toNode_ne_leaf P.lower l (Subtype.ext (hv.trans he).symm)
  have hc₁ : (p.1.1,p.1.2 ++ [i]) ≠ (G.pair P.retained).1 := fun he => hl (Subtype.ext (hv.trans he))
  rw [hv]
  exact exchangeAddress_child _ _ _ _ _ (branch_ne_paired_address G P p) hc₀ hc₁

end WaveTurbulence.Twist
