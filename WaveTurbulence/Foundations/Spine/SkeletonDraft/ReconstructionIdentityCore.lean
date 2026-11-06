/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentityRaw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # Literal identity data and their exact core addresses -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eq_identity_of_nil_triv {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (ht : ∀ b, D.tree b = .nil) (hc : ∀ p, D.couple p = .triv) :
    D = ReconstructionData.identity S := by
  have htree : D.tree = fun _ => .nil := funext ht
  have hcouple : D.couple = fun _ => .triv := funext hc
  cases D
  cases htree
  cases hcouple
  rfl

theorem ReconstructionData.identity_corePosition {w : ℕ} (S : Garden w) (b : GBranch S.tree) :
    (ReconstructionData.identity S).corePosition b = b.1 := by
  rw [ReconstructionData.corePosition,inflatedPosition_identity]
  simp only [ReconstructionData.identity,RegChain.lonePath,addrExt,List.append_nil]
  rfl

end WaveTurbulence.Reg.Skeleton
