/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementFamilyCount

/-! # Uniform prefix-word bound for assignments at actual source skeleton slots -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Total branching order of all regular replacements, excluding the original skeleton. -/
noncomputable def ReconstructionData.size {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ℕ :=
  (∑ b, (D.tree b).size) + ∑ p, (D.couple p).size

/-- Enumerate the actual fixed source slots solely for finite counting. -/
noncomputable def ReconstructionData.family {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    ReplacementFamily (Fintype.card (GBranch S.tree)) (Fintype.card (SourcePair S)) where
  trees := fun i => D.tree ((Fintype.equivFin (GBranch S.tree)).symm i)
  couples := fun i => D.couple ((Fintype.equivFin (SourcePair S)).symm i)
  trees_wf := fun _ => D.tree_wf _
  couples_wf := fun _ => D.couple_wf _

theorem ReconstructionData.family_size {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    D.family.size = D.size := by
  classical
  exact congrArg₂ (· + ·)
    (Equiv.sum_comp (Fintype.equivFin (GBranch S.tree)).symm (fun b => (D.tree b).size))
    (Equiv.sum_comp (Fintype.equivFin (SourcePair S)).symm (fun p => (D.couple p).size))

theorem ReconstructionData.family_injective {w : ℕ} (S : Garden w) :
    Function.Injective (ReconstructionData.family (S := S)) := by
  classical
  intro D E he
  have ht : D.tree = E.tree := by
    funext b
    have hh := congrFun (congrArg ReplacementFamily.trees he) ((Fintype.equivFin (GBranch S.tree)) b)
    simpa only [ReconstructionData.family,Equiv.symm_apply_apply] using hh
  have hc : D.couple = E.couple := by
    funext p
    have hh := congrFun (congrArg ReplacementFamily.couples he) ((Fintype.equivFin (SourcePair S)) p)
    simpa only [ReconstructionData.family,Equiv.symm_apply_apply] using hh
  cases D
  cases E
  cases ht
  cases hc
  rfl

/-- Bound on actual skeleton replacement assignments, with every root sign already fixed by S. -/
theorem reconstructionDataCount_le {w : ℕ} (S : Garden w) (m : ℕ) :
    Nat.card {D : ReconstructionData S // D.size ≤ m} ≤
      12 ^ (4*m + Fintype.card (GBranch S.tree) + Fintype.card (SourcePair S)) := by
  classical
  let f : {D : ReconstructionData S // D.size ≤ m} →
      {D : ReplacementFamily (Fintype.card (GBranch S.tree)) (Fintype.card (SourcePair S)) // D.size ≤ m} :=
    fun D => ⟨D.1.family,by rw [ReconstructionData.family_size]; exact D.2⟩
  have hf : Function.Injective f := by
    intro D E he
    exact Subtype.ext (ReconstructionData.family_injective S (congrArg Subtype.val he))
  exact (Nat.card_le_card_of_injective f hf).trans (replacementFamilyCount_le _ _ m)

end WaveTurbulence.Reg.Skeleton
