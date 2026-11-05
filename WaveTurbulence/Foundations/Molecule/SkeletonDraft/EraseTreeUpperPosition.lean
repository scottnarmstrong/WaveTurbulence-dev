/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionTreeUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionLocalCongruence

/-! # Erasing a tree context preserves its own upper boundary and every outside attachment -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_position_at {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b : GBranch S.tree) :
    inflatedPosition S (D.eraseTree b).tree b.toNode = inflatedPosition S D.tree b.toNode := by
  apply inflatedPosition_congr_ancestors
  intro c _ hc
  apply D.eraseTree_other
  intro he
  subst c
  change b.1.2.length < b.1.2.length at hc
  omega

theorem ReconstructionData.eraseTree_position_of_not_below {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b : GBranch S.tree) (a : GNode S.tree)
    (ha : ¬ Below b.1 a.1) :
    inflatedPosition S (D.eraseTree b).tree a = inflatedPosition S D.tree a := by
  apply inflatedPosition_congr_ancestors
  intro c hc _
  exact D.eraseTree_other b c (fun he => ha (he ▸ hc))

end WaveTurbulence.Reg.Skeleton
