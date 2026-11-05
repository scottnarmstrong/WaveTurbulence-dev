/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataExt

/-! # Literal updates of one actual source leaf-pair replacement slot -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def ReconstructionData.withCouple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (p : SourcePair S) (Q : RegCpl) (hQ : Q.wf = true) : ReconstructionData S where
  tree := D.tree
  couple := Function.update D.couple p Q
  tree_wf := D.tree_wf
  couple_wf := by
    intro q
    by_cases hq : q = p
    · subst q
      simpa only [Function.update_self] using hQ
    · simpa only [Function.update_of_ne hq] using D.couple_wf q

noncomputable def ReconstructionData.eraseCouple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (p : SourcePair S) : ReconstructionData S := D.withCouple p .triv rfl

theorem ReconstructionData.eraseCouple_at {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (p : SourcePair S) : (D.eraseCouple p).couple p = .triv := Function.update_self _ _ _

theorem ReconstructionData.eraseCouple_other {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (p q : SourcePair S) (hq : q ≠ p) : (D.eraseCouple p).couple q = D.couple q :=
  Function.update_of_ne hq _ _

theorem ReconstructionData.eraseCouple_eq_self {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (p : SourcePair S) (hp : D.couple p = .triv) : D.eraseCouple p = D := by
  have he : Function.update D.couple p .triv = D.couple := by
    rw [← hp]
    exact Function.update_eq_self _ _
  exact ReconstructionData.ext_tree_couple _ _ rfl he

end WaveTurbulence.Reg.Skeleton
