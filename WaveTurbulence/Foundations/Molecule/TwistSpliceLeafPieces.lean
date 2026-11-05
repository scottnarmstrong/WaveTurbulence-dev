/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistBoundaryAddresses

/-! # The concrete retained-leaf diagram for the two CL splicings

TARGET twistexplain (c): leaf pieces are compared at actual addresses,
so pairing equality is a consequence of the garden pairing conjugacy.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Evaluate the accepted actual splice leaf bijection on its concrete leaf pieces. -/
theorem spliceLeafEquiv_piece {w : ℕ} {G : Garden w} {a : GBranch G.tree}
    (B : Mole.SpliceBoundaryRoots G a) (p : Mole.SpliceLeafPiece B) :
    (Mole.spliceLeafEquiv B (Mole.splicePieceNew B p)).1 = Mole.splicePieceOld B p := by
  let e := Equiv.ofBijective (Mole.splicePieceNew B)
    ⟨Mole.splicePieceNew_injective B,Mole.splicePieceNew_surjective B⟩
  exact congrArg (Mole.splicePieceOld B) (e.symm_apply_apply p)

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- Actual leaves outside the upper splice site retain their exact address. -/
theorem coreLeafEquiv_outside_upper_val (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (l : GLeaf G.tree) (hout : ¬ a.toNode.IsDesc l.toNode) : (coreLeafEquiv G P l).1 = l.1 := by
  have hb := (Mole.cl_parent_strict_descendant G hB hCL).1
  have hp := placement_pair_below_upper G P hB hCL hP
  have hn : ¬ (l.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: l.1.2) := by
    intro hd
    exact hout ⟨hb.1.trans hd.1.symm,hb.2.trans hd.2⟩
  have he : l.1 ≠ (G.pair P.retained).1 := by
    intro he
    have hnode : l.toNode = (G.pair P.retained).toNode := Subtype.ext he
    exact hout (hnode.symm ▸ hp)
  have hh := coreLeafEquiv_address G P l
  exact hh.trans (by simp [exchangeAddress,hn,he])

/-- The explicit new leaf piece corresponding to an old retained splice piece. -/
@[expose] noncomputable def twistedSpliceLeafPiece (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    Mole.SpliceLeafPiece (originalSpliceBoundary G P hB hCL D) →
      Mole.SpliceLeafPiece (twistedSpliceBoundary G P hB hCL hP D)
  | .inl l => .inl ⟨coreLeafEquiv G P l.1,by
      intro hd
      have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
      have fl := coreLeafEquiv_outside_upper_val G P hB hCL hP l.1 l.2
      change (coreBranchEquiv G P a).1.1 = (coreLeafEquiv G P l.1).1.1 ∧
        (coreBranchEquiv G P a).1.2 <+: (coreLeafEquiv G P l.1).1.2 at hd
      rw [fa,fl] at hd
      exact l.2 hd⟩
  | .inr ⟨i,q⟩ => .inr ⟨i,⟨q.1,by
      rw [unitTwist_boundarySubtree G P hB hCL hP D i]
      exact q.2⟩⟩

/-- Corresponding pieces occupy identical addresses in the two equal spliced forests. -/
theorem twistedSpliceLeafPiece_new_val (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (p : Mole.SpliceLeafPiece (originalSpliceBoundary G P hB hCL D)) :
    (Mole.splicePieceNew (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceLeafPiece G P hB hCL hP D p)).1 =
      (Mole.splicePieceNew (originalSpliceBoundary G P hB hCL D) p).1 := by
  cases p with
  | inl l => exact coreLeafEquiv_outside_upper_val G P hB hCL hP l.1 l.2
  | inr p =>
    obtain ⟨i,q⟩ := p
    change ((coreBranchEquiv G P a).1.1,(coreBranchEquiv G P a).1.2 ++ i::q.1) = (a.1.1,a.1.2 ++ i::q.1)
    rw [selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1]

/-- Pulling a leaf piece back to the original garden commutes with the actual unit twist. -/
theorem twistedSpliceLeafPiece_old (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (p : Mole.SpliceLeafPiece (originalSpliceBoundary G P hB hCL D)) :
    coreLeafEquiv G P (Mole.splicePieceOld (originalSpliceBoundary G P hB hCL D) p) =
      Mole.splicePieceOld (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceLeafPiece G P hB hCL hP D p) := by
  cases p with
  | inl l => rfl
  | inr p =>
    obtain ⟨i,q⟩ := p
    apply Subtype.ext
    have he := coreLeafEquiv_address G P (Mole.splicePieceOld (originalSpliceBoundary G P hB hCL D) (.inr ⟨i,q⟩))
    exact he.trans (unitTwist_boundary_address_append G P hB hCL hP D i q.1)

end WaveTurbulence.Twist
