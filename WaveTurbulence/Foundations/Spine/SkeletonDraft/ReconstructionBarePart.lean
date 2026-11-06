/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BareInflation

/-! # The literal bare-chain intermediate of arbitrary regular replacement data -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Erase all regular couple decorations, retaining the exact legal bare branch chains. -/
noncomputable def ReconstructionData.barePart {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) : ReconstructionData S where
  tree := fun b => eraseChainCouples (D.tree b)
  couple := fun _ => .triv
  tree_wf := fun b => bareChain_wf (eraseChainCouples (D.tree b)) (eraseChainCouples_bare _)
  couple_wf := fun _ => rfl

theorem ReconstructionData.barePart_isBare {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    D.barePart.IsBareInflation := ⟨fun b => eraseChainCouples_bare _,fun _ => rfl⟩

theorem ReconstructionData.barePart_position {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (a : GNode S.tree) : inflatedPosition S D.barePart.tree a = inflatedPosition S D.tree a := by
  by_cases hp : a.1.2 = []
  · conv_lhs => rw [inflatedPosition,dite_eq_left hp]
    conv_rhs => rw [inflatedPosition,dite_eq_left hp]
  · conv_lhs => rw [inflatedPosition,dite_eq_right hp]
    conv_rhs => rw [inflatedPosition,dite_eq_right hp]
    exact congrArg₂ addrExt (D.barePart_position (a.parent hp).toNode)
      (congrArg (fun p => p ++ [a.1.2.getLast hp]) (eraseChainCouples_lonePath (D.tree (a.parent hp))))
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  rw [List.length_dropLast]
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  omega

theorem ReconstructionData.barePart_corePosition {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : D.barePart.corePosition b = D.corePosition b :=
  congrArg₂ addrExt (D.barePart_position b.toNode) (eraseChainCouples_lonePath (D.tree b))

end WaveTurbulence.Reg.Skeleton
