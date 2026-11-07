/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue1
import Mathlib.Tactic

/-!
# Reversal of a true-choice LF operation: bases and data

The reverse source has the same normalized base as the original source and its reconstruction data
agree (up to the cast `unitTwistGarden_involutive`) with those of the original.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem corePlacement_cast_eq {G1 G2 : Garden w} (e : G1 = G2) (P1 : CorePlacement G1) (P2 : CorePlacement G2)
    (hl : P1.lower.1 = P2.lower.1) (hk : P1.keep = P2.keep) : (e ▸ P1 : CorePlacement G2) = P2 := by
  subst e
  have hlow : P1.lower = P2.lower := Subtype.ext hl
  have a1 : P1.retained.1 = (P1.lower.1.1, P1.lower.1.2 ++ [P1.keep]) :=
    congrArg (fun n : GNode G1.tree => n.1) P1.child
  have a2 : P2.retained.1 = (P2.lower.1.1, P2.lower.1.2 ++ [P2.keep]) :=
    congrArg (fun n : GNode G1.tree => n.1) P2.child
  have hret : P1.retained = P2.retained := by
    apply Subtype.ext
    rw [a1, a2, hl, hk]
  cases P1
  cases P2
  simp only at hlow hret hk
  subst hlow hret hk
  rfl


section Place
variable {S G : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
  (P : CorePlacement S) (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)

theorem reverse_expanded_lower_val :
    (reversePlacement G (expandedPlacement D hS hd P hq)).lower.1 =
      inflatedPosition S D.tree (S.pair P.retained).toNode := by
  show (coreBranchEquiv G (expandedPlacement D hS hd P hq) (expandedPlacement D hS hd P hq).lower).1 = _
  rw [coreBranchEquiv_lower_val]
  show (G.pair (decodedTrivLeaf D hS hd P.retained hq)).1 = _
  rw [decodedTrivLeaf_pair D hS hd P.retained hq]
  rfl

theorem twist_lower_inflated :
    inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
      (coreBranchEquiv S P P.lower).toNode = inflatedPosition S D.tree (S.pair P.retained).toNode := by
  refine (inflatedPosition_eq_rawSourcePosition (S := unitTwistGarden S P) (twistReconstruction S P hS D)
    (coreBranchEquiv S P P.lower).toNode).trans (Eq.trans ?_ (inflatedPosition_eq_rawSourcePosition D _).symm)
  have hout : ¬ Below P.lower.toNode.1 (S.pair P.retained).1 := fun hb => P.paired_outside ⟨hb.1.symm, hb.2⟩
  have hmem : (S.pair P.retained).1.2 ∈ ((commonForest S P.lower) (S.pair P.retained).1.1).leaves :=
    (collapseNodeForest_leaf_iff S.tree P.lower.toNode (S.pair P.retained).1).mpr
      (Or.inl ⟨(S.pair P.retained).2, hout⟩)
  have := common_rawSourcePosition_twist S P hS D
    ⟨(S.pair P.retained).1, TTree.leaves_subset_nodes _ hmem⟩
  have e : (coreBranchEquiv S P P.lower).toNode.1 = (S.pair P.retained).1 := coreBranchEquiv_lower_val S P
  rw [e]
  exact this

end Place

end WaveTurbulence.Stage1
