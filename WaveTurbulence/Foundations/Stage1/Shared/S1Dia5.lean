/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia4
import Mathlib.Tactic

/-!
# Diamond for a `false` operation at `i` and a `true` operation at `j`: the final data agree
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.diamondFT_data (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true) :
    (show ReconstructionData (unitTwistGarden A.skeleton (A.family.placement j)) from (P.specF con hj).FD) =
      (show ReconstructionData (unitTwistGarden A.skeleton (A.family.placement j)) from (P.swap.specT hj con).FD) := by
  have hne : (A.family.placement i).lower ≠ (A.family.placement j).lower := CoreFamily.lower_ne_of_ne A.family P.hij
  apply ReconstructionData.ext_tree_couple
  · funext b'
    obtain ⟨b, rfl⟩ := (coreBranchEquiv A.skeleton (A.family.placement j)).surjective b'
    have e1 : ((P.srcJF con).finalData true hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).tree
        (coreBranchEquiv A.skeleton (A.family.placement j) b) =
        if b = (A.family.placement j).lower then hj.newTree else con.data.tree b :=
      finalData_tree_true (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
    have e3 : con.data.tree b = if b = (A.family.placement i).lower then con.newTree else A.data.tree b :=
      finalData_tree_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf b
    have e2 : ((P.swap.srcJT hj).finalData false con.newTree con.newCouple con.tree_wf con.couple_wf).tree
        (coreBranchEquiv A.skeleton (A.family.placement j) b) =
        if coreBranchEquiv A.skeleton (A.family.placement j) b =
            coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement i).lower
          then con.newTree else hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j) b) := by
      have := finalData_tree_false (P.swap.srcJT hj) con.newTree con.newCouple con.tree_wf con.couple_wf
        (coreBranchEquiv A.skeleton (A.family.placement j) b)
      have hl : (P.swap.srcJT hj).placement.lower =
          coreBranchEquiv A.skeleton (A.family.placement j) (A.family.placement i).lower :=
        CoreFamily.nextPlacement_lower A.family j i
      rw [this, hl]
      rfl
    have e4 : hj.data.tree (coreBranchEquiv A.skeleton (A.family.placement j) b) =
        if b = (A.family.placement j).lower then hj.newTree else A.data.tree b :=
      finalData_tree_true P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf b
    refine e1.trans (Eq.trans ?_ e2.symm)
    have hinj : ∀ b₁ b₂, coreBranchEquiv A.skeleton (A.family.placement j) b₁ =
        coreBranchEquiv A.skeleton (A.family.placement j) b₂ ↔ b₁ = b₂ := fun b₁ b₂ =>
      (coreBranchEquiv A.skeleton (A.family.placement j)).injective.eq_iff
    rw [e3, e4]
    simp only [hinj]
    by_cases h1 : b = (A.family.placement j).lower
    · have h2 : b ≠ (A.family.placement i).lower := fun he => hne (he.symm.trans h1)
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : b = (A.family.placement i).lower
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  · funext q'
    obtain ⟨q, rfl⟩ : ∃ q : SourcePair A.skeleton, P.srcJ.pairs true q = q' := (P.srcJ.pairs true).surjective q'
    have hne' : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠
        pairOfLeaf A.skeleton A.plain (A.family.placement j).retained :=
      CoreFamily.exceptional_ne A.family A.plain P.hij
    have e1 : ((P.srcJF con).finalData true hj.newTree hj.newCouple hj.tree_wf hj.couple_wf).couple
        (P.srcJ.pairs true q) =
        if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
          else con.data.couple q :=
      finalData_couple_true (P.srcJF con) hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
    have e3 : con.data.couple q = if q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
        then con.newCouple else A.data.couple q :=
      finalData_couple_false P.srcI con.newTree con.newCouple con.tree_wf con.couple_wf q
    have e2 : ((P.swap.srcJT hj).finalData false con.newTree con.newCouple con.tree_wf con.couple_wf).couple
        (P.srcJ.pairs true q) =
        if P.srcJ.pairs true q = P.srcJ.pairs true (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)
          then con.newCouple else hj.data.couple (P.srcJ.pairs true q) := by
      have := finalData_couple_false (P.swap.srcJT hj) con.newTree con.newCouple con.tree_wf con.couple_wf
        (P.srcJ.pairs true q)
      rw [this, P.swap.exc_cross hj]
      rfl
    have e4 : hj.data.couple (P.srcJ.pairs true q) =
        if q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained then hj.newCouple
          else A.data.couple q :=
      finalData_couple_true P.srcJ hj.newTree hj.newCouple hj.tree_wf hj.couple_wf q
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [e3, e4]
    have hinj : ∀ q1 q2 : SourcePair A.skeleton, P.srcJ.pairs true q1 = P.srcJ.pairs true q2 ↔ q1 = q2 :=
      fun _ _ => (P.srcJ.pairs true).injective.eq_iff
    simp only [hinj]
    by_cases h1 : q = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
    · have h2 : q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained := fun he => hne' (he.symm.trans h1)
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : q = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

end WaveTurbulence.Stage1
