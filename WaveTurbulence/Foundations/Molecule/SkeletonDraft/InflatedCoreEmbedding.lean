/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionInjective

/-! # Injective survival of every actual core branch under literal reconstruction -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.corePosition_ne_of_desc {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (a b : GBranch S.tree) (hab : Below a.1 b.1) (hne : a ≠ b) : D.corePosition a ≠ D.corePosition b := by
  have hn : a.toNode ≠ b.toNode := fun he => hne (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) he))
  obtain ⟨i,hi⟩ := below_child_of_desc_ne a b.toNode hab hn
  have ht := inflatedPosition_below S D.tree (a.child i) b.toNode hi
  rw [D.core_child_position] at ht
  have hb : Below (addrExt (D.corePosition a) [i]) (D.corePosition b) :=
    below_trans ht (below_extend _ _)
  exact (below_child_ne_root (D.corePosition a) (D.corePosition b) i [] hb).symm

/-- The original source core branches remain distinct even when replacement trees are empty. -/
theorem ReconstructionData.corePosition_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    Function.Injective D.corePosition := by
  intro a b he
  by_contra hn
  by_cases hab : Below a.1 b.1
  · exact D.corePosition_ne_of_desc a b hab hn he
  by_cases hba : Below b.1 a.1
  · exact D.corePosition_ne_of_desc b a hba (Ne.symm hn) he.symm
  have hp := inflatedPosition_incomp S D.tree a.toNode b.toNode ⟨hab,hba⟩
  have hc : IncompAddr (D.corePosition a) (D.corePosition b) := hp.descendants (below_extend _ _) (below_extend _ _)
  apply hc.1
  rw [he]
  exact ⟨rfl,List.prefix_refl _⟩

end WaveTurbulence.Reg.Skeleton
