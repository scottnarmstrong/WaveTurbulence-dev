/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceBranchEquiv
import Mathlib.Tactic

/-! # Pointwise equations for the constructed atom transport -/

public section
namespace WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

theorem spliceNonCrownBranchEquiv_piece (p : SpliceBranchPiece B) :
    (spliceNonCrownBranchEquiv B ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩).1 =
      spliceBranchPieceOld B p := by
  let e : SpliceBranchPiece B ≃ {c : GBranch (spliceForest G a B.node) // c ≠ spliceCrownBranch B} :=
    Equiv.ofBijective (fun p : SpliceBranchPiece B =>
      ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩)
    ⟨fun p q he => spliceBranchPieceNew_injective B (congrArg Subtype.val he),by
      intro c
      obtain ⟨p,hp⟩ := spliceBranchPieceNew_surjective_except_crown B c.1 c.2
      exact ⟨p,Subtype.ext hp⟩⟩
  have he : e.symm ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩ = p := e.symm_apply_apply p
  change spliceBranchPieceOld B (e.symm ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩) = _
  exact congrArg (spliceBranchPieceOld B) he

theorem spliceBranchOptionEquiv_piece (p : SpliceBranchPiece B) :
    spliceBranchOptionEquiv B (spliceBranchPieceNew B p) =
      some ⟨spliceBranchPieceOld B p,spliceBranchPieceOld_retained B p⟩ := by
  let e := Equiv.optionSubtypeNe (spliceCrownBranch B)
  have he : e.symm (spliceBranchPieceNew B p) =
      some ⟨spliceBranchPieceNew B p,spliceBranchPieceNew_ne_crown B p⟩ := e.symm_apply_eq.mpr rfl
  change Equiv.optionCongr (spliceNonCrownBranchEquiv B) (e.symm (spliceBranchPieceNew B p)) = _
  rw [he]
  apply congrArg some
  apply Subtype.ext
  exact spliceNonCrownBranchEquiv_piece B p

end WaveTurbulence.Mole
