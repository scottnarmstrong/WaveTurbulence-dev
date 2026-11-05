/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreBranchSigns

/-! # Exact positions of the three exchanged nodes

TARGET twist: u2 moves to u0, u0 moves to u2, and u23 keeps its
ordered position as a child of u2. These coordinate identities support
the reverse operation and the bond-label exchange.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The lower branching root moves to the old paired leaf position. -/
theorem coreBranchEquiv_lower_val : (coreBranchEquiv G P P.lower).1 = (G.pair P.retained).1 := by
  have he : P.lower = (coreBranchPiece G P).symm (.inr (lowerLocalBranch G P)) := by
    rw [← coreBranchPiece_lower,Equiv.symm_apply_apply]
  rw [he,coreBranchEquiv_piece]
  change ((pairedHole G P).1.1,(pairedHole G P).1.2 ++ []) = (G.pair P.retained).1
  simp only [List.append_nil]
  rfl

/-- The retained leaf moves with the crown and stays in its original outer slot. -/
theorem coreLeafEquiv_retained_val : (coreLeafEquiv G P P.retained).1 =
    ((G.pair P.retained).1.1,(G.pair P.retained).1.2 ++ [P.keep]) := by
  have he : P.retained = (coreLeafPiece G P).symm (.inr (keptLocalLeaf G P)) := by
    rw [← coreLeafPiece_retained,Equiv.symm_apply_apply]
  conv_lhs => rw [he]
  rw [coreLeafEquiv_piece]
  change ((pairedHole G P).1.1,(pairedHole G P).1.2 ++ [freeSwap P.keep P.keep]) = _
  rw [freeSwap_keep P.keep P.outer]
  rfl

/-- The old paired leaf moves to the old lower branching root position. -/
theorem coreLeafEquiv_paired_val : (coreLeafEquiv G P (G.pair P.retained)).1 = P.lower.1 := by
  have he : G.pair P.retained = (coreLeafPiece G P).symm (.inl (pairedOutsideLeaf G P)) := by
    rw [← coreLeafPiece_paired,Equiv.symm_apply_apply]
  rw [he,coreLeafEquiv_piece]
  change (Equiv.swap (collapsedRoot G P.lower) (pairedHole G P) (pairedHole G P)).1 = _
  rw [Equiv.swap_apply_right]
  rfl

/-- The reverse concrete placement in the actual twisted garden. -/
@[expose] noncomputable def reversePlacement : CorePlacement (unitTwistGarden G P) where
  lower := coreBranchEquiv G P P.lower
  retained := coreLeafEquiv G P P.retained
  nonroot := by
    change (coreBranchEquiv G P P.lower).1.2 ≠ []
    rw [coreBranchEquiv_lower_val]
    exact P.paired_nonroot
  paired_nonroot := by
    rw [unitTwistGarden_pair]
    change (coreLeafEquiv G P (G.pair P.retained)).1.2 ≠ []
    rw [coreLeafEquiv_paired_val]
    exact P.nonroot
  keep := P.keep
  unmarked := by rw [unitTwistGarden_mark]; exact P.unmarked
  child := by
    apply Subtype.ext
    change (coreLeafEquiv G P P.retained).1 =
      ((coreBranchEquiv G P P.lower).1.1,(coreBranchEquiv G P P.lower).1.2 ++ [P.keep])
    rw [coreLeafEquiv_retained_val,coreBranchEquiv_lower_val]
  outer := P.outer
  paired_outside := by
    rw [unitTwistGarden_pair]
    intro hd
    change (coreBranchEquiv G P P.lower).1.1 = (coreLeafEquiv G P (G.pair P.retained)).1.1 ∧
      (coreBranchEquiv G P P.lower).1.2 <+: (coreLeafEquiv G P (G.pair P.retained)).1.2 at hd
    rw [coreBranchEquiv_lower_val,coreLeafEquiv_paired_val] at hd
    have hleaf : P.lower.1.2 ∈ (commonForest G P.lower (G.pair P.retained).1.1).leaves :=
      hd.1.symm ▸ (collapsedRoot G P.lower).2
    have hp := leaf_prefix_eq (pairedHole G P).2 hleaf hd.2
    exact pairedHole_ne_root G P (Subtype.ext (Prod.ext hd.1 hp))

end WaveTurbulence.Twist
