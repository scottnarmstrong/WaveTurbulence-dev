/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # Fixed embedded core addresses fix every ordered attachment boundary -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem inflatedPosition_eq_of_corePosition_eq {w : ℕ} {S : Garden w}
    (D E : ReconstructionData S) (hc : ∀ b, D.corePosition b = E.corePosition b)
    (a : GNode S.tree) : inflatedPosition S D.tree a = inflatedPosition S E.tree a := by
  by_cases hp : a.1.2 = []
  · have ha : a = GNode.root S.tree a.1.1 := Subtype.ext (Prod.ext rfl hp)
    rw [ha,inflatedPosition_root,inflatedPosition_root]
  · have hd := D.core_child_position (a.parent hp) (a.1.2.getLast hp)
    have he := E.core_child_position (a.parent hp) (a.1.2.getLast hp)
    rw [child_parent] at hd he
    exact hd.trans ((congrArg (fun z => addrExt z [a.1.2.getLast hp]) (hc (a.parent hp))).trans he.symm)

end WaveTurbulence.Reg.Skeleton
