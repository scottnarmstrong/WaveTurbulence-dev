/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BareInflation

/-! # Literal updates of one actual skeleton branch replacement -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def ReconstructionData.withTree {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) (X : RegChain) (hX : X.wf = true) : ReconstructionData S where
  tree := Function.update D.tree b X
  couple := D.couple
  tree_wf := by
    intro c
    by_cases hc : c = b
    · subst c
      simpa only [Function.update_self] using hX
    · simpa only [Function.update_of_ne hc] using D.tree_wf c
  couple_wf := D.couple_wf

/-- Remove just one regular-tree context, retaining all ordered source slots. -/
noncomputable def ReconstructionData.eraseTree {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : ReconstructionData S := D.withTree b .nil rfl

theorem ReconstructionData.eraseTree_at {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : (D.eraseTree b).tree b = .nil := Function.update_self _ _ _

theorem ReconstructionData.eraseTree_other {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b c : GBranch S.tree) (hc : c ≠ b) : (D.eraseTree b).tree c = D.tree c :=
  Function.update_of_ne hc _ _

theorem ReconstructionData.IsBareInflation.eraseTree {w : ℕ} {S : Garden w}
    {D : ReconstructionData S} (hD : D.IsBareInflation) (b : GBranch S.tree) :
    (D.eraseTree b).IsBareInflation := by
  refine ⟨?_,hD.2⟩
  intro c
  by_cases hc : c = b
  · subst c
    rw [D.eraseTree_at]
    trivial
  · rw [D.eraseTree_other b c hc]
    exact hD.1 c

end WaveTurbulence.Reg.Skeleton
