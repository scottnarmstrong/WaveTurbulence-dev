/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceBranchNewTransport
public import WaveTurbulence.Foundations.Molecule.SpliceBranchOldTransport
public import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic

/-! # The spliced branch carrier is one crown plus retained old branches
TARGET `block_clcn` (2), actual atom-carrier part of the contraction.
-/

public section
namespace WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

/-- Equivalence away from the single retained crown. -/
@[expose] noncomputable def spliceNonCrownBranchEquiv :
    {c : GBranch (spliceForest G a B.node) // c ≠ spliceCrownBranch B} ≃
      {c : GBranch G.tree // IsSpliceRetainedBranch B c} :=
  (Equiv.ofBijective (fun p : SpliceBranchPiece B =>
      ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩)
    ⟨fun p q he => spliceBranchPieceNew_injective B (congrArg Subtype.val he),by
      intro c
      obtain ⟨p,hp⟩ := spliceBranchPieceNew_surjective_except_crown B c.1 c.2
      exact ⟨p,Subtype.ext hp⟩⟩).symm.trans
    (Equiv.ofBijective (fun p => ⟨spliceBranchPieceOld B p,spliceBranchPieceOld_retained B p⟩)
      ⟨fun p q he => spliceBranchPieceOld_injective B (congrArg Subtype.val he),by
        intro c
        obtain ⟨p,hp⟩ := spliceBranchPieceOld_surjective_retained B c.1 c.2
        exact ⟨p,Subtype.ext hp⟩⟩)

/-- The crown is `none`, and each other branch keeps its actual old name. -/
@[expose] noncomputable def spliceBranchOptionEquiv :
    GBranch (spliceForest G a B.node) ≃ Option {c : GBranch G.tree // IsSpliceRetainedBranch B c} :=
  (Equiv.optionSubtypeNe (spliceCrownBranch B)).symm.trans
    (Equiv.optionCongr (spliceNonCrownBranchEquiv B))

theorem spliceBranchOptionEquiv_crown : spliceBranchOptionEquiv B (spliceCrownBranch B) = none := by
  change Equiv.optionCongr (spliceNonCrownBranchEquiv B)
    ((Equiv.optionSubtypeNe (spliceCrownBranch B)).symm (spliceCrownBranch B)) = none
  have h : (Equiv.optionSubtypeNe (spliceCrownBranch B)).symm (spliceCrownBranch B) = none :=
    (Equiv.optionSubtypeNe (spliceCrownBranch B)).symm_apply_eq.mpr rfl
  rw [h]
  rfl

end WaveTurbulence.Mole
