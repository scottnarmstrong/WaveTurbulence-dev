/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia12
import Mathlib.Tactic

/-!
# Diamond for two `true` operations: the final data agree (HEq)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.TT_skel (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    (P.opJT con hj).output.skeleton = (P.swap.opJT hj con).output.skeleton :=
  congrArg (fun s : FamilyState w ι => s.1) (P.TT_famstate con hj)

theorem PairCtx.TT_castBranch (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b : GBranch A.skeleton.tree) :
    castBranch (P.TT_skel con hj) ((P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b)) =
      (P.swap.srcJT hj).branches true (coreBranchEquiv A.skeleton (A.family.placement j) b) :=
  Subtype.ext (doubleBranch_commute_addr (A := A) P.hij b)

theorem PairCtx.TT_data_tree (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (b1 : GBranch (P.opJT con hj).output.skeleton.tree) :
    (P.opJT con hj).output.data.tree b1 =
      (P.swap.opJT hj con).output.data.tree (castBranch (P.TT_skel con hj) b1) := by
  obtain ⟨b, hb⟩ := ((coreBranchEquiv A.skeleton (A.family.placement i)).trans
    ((P.srcJT con).branches true)).surjective b1
  have hb' : b1 = (P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b) := hb.symm
  rw [hb']
  have e1 := P.TT_FD_tree con hj b
  have e2 := P.swap.TT_FD_tree hj con b
  have e3 := P.TT_castBranch con hj b
  have hne : (A.family.placement i).lower ≠ (A.family.placement j).lower := CoreFamily.lower_ne_of_ne A.family P.hij
  have hF : (if b = (A.family.placement j).lower then hj.newTree
      else if b = (A.family.placement i).lower then con.newTree else A.data.tree b) =
      (if b = (A.family.placement i).lower then con.newTree
      else if b = (A.family.placement j).lower then hj.newTree else A.data.tree b) := by
    by_cases h1 : b = (A.family.placement j).lower
    · have h2 : b ≠ (A.family.placement i).lower := fun he => hne (he.symm.trans h1)
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : b = (A.family.placement i).lower
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  exact e1.trans (hF.trans (e2.symm.trans (congrArg (P.swap.opJT hj con).output.data.tree e3.symm)))

theorem sourcePairAt_cast {S S' : Garden w} (hs : S = S') (l : GLeaf S.tree) (l' : GLeaf S'.tree)
    (h : l.1 = l'.1) : sourcePairAt S l = sourcePairAt S' l' := by
  subst hs
  have : l = l' := Subtype.ext h
  subst this
  rfl

theorem PairCtx.TT_data_couple (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true)
    (q1 : SourcePair (P.opJT con hj).output.skeleton) :
    (P.opJT con hj).output.data.couple q1 =
      (P.swap.opJT hj con).output.data.couple (castPair (P.TT_skel con hj) q1) := by
  have hS1 : (P.opJT con hj).output.skeleton.IsPlain := (P.opJT con hj).output.plain
  let E : GLeaf A.skeleton.tree ≃ GLeaf (P.opJT con hj).output.skeleton.tree :=
    (coreLeafEquiv A.skeleton (A.family.placement i)).trans (chosenLeafEquiv (P.srcJT con).skeleton (P.srcJT con).placement true)
  obtain ⟨ℓ, hℓ⟩ := E.surjective (q1.firstLeaf hS1)
  have hq1 : q1 = pairOfLeaf _ hS1 (E ℓ) := by
    rw [hℓ]; exact (pairOfLeaf_firstLeaf _ hS1 q1).symm
  rw [hq1]
  set qA := pairOfLeaf A.skeleton A.plain ℓ with hqA
  have h1 : (P.srcJT con).pairs true (P.srcI.pairs true qA) = pairOfLeaf _ hS1 (E ℓ) := by
    have a1 : P.srcI.pairs true qA = pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
        (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) ℓ) :=
      sourcePairEquiv_pairOfLeaf P.srcI.plain (P.srcI.chosen_plain true) (chosenLeafEquiv _ _ true)
        (chosenLeafEquiv_pair _ _ true) ℓ
    rw [a1]
    exact sourcePairEquiv_pairOfLeaf _ ((P.srcJT con).chosen_plain true) (chosenLeafEquiv _ _ true)
      (chosenLeafEquiv_pair _ _ true) _
  have h2 := P.TT_FD_couple con hj qA
  rw [h1] at h2
  refine h2.trans ?_
  let E' : GLeaf A.skeleton.tree ≃ GLeaf (P.swap.opJT hj con).output.skeleton.tree :=
    (coreLeafEquiv A.skeleton (A.family.placement j)).trans
      (chosenLeafEquiv (P.swap.srcJT hj).skeleton (P.swap.srcJT hj).placement true)
  have hS2 : (P.swap.opJT hj con).output.skeleton.IsPlain := (P.swap.opJT hj con).output.plain
  have h3 : castPair (P.TT_skel con hj) (pairOfLeaf _ hS1 (E ℓ)) = pairOfLeaf _ hS2 (E' ℓ) := by
    apply Subtype.ext
    exact sourcePairAt_cast (P.TT_skel con hj) _ _ (doubleLeaf_commute_addr (A := A) P.hij ℓ)
  rw [h3]
  have h4 : (P.swap.srcJT hj).pairs true (P.swap.srcI.pairs true qA) = pairOfLeaf _ hS2 (E' ℓ) := by
    have a1 : P.swap.srcI.pairs true qA = pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement j))
        (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement j) ℓ) :=
      sourcePairEquiv_pairOfLeaf P.swap.srcI.plain (P.swap.srcI.chosen_plain true) (chosenLeafEquiv _ _ true)
        (chosenLeafEquiv_pair _ _ true) ℓ
    rw [a1]
    exact sourcePairEquiv_pairOfLeaf _ ((P.swap.srcJT hj).chosen_plain true) (chosenLeafEquiv _ _ true)
      (chosenLeafEquiv_pair _ _ true) _
  have h5 := P.swap.TT_FD_couple hj con qA
  rw [h4] at h5
  refine Eq.trans ?_ h5.symm
  have hne' : pairOfLeaf A.skeleton A.plain (A.family.placement i).retained ≠
      pairOfLeaf A.skeleton A.plain (A.family.placement j).retained := CoreFamily.exceptional_ne A.family A.plain P.hij
  by_cases c1 : qA = pairOfLeaf A.skeleton A.plain (A.family.placement j).retained
  · have c2 : qA ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained := fun he => hne' (he.symm.trans c1)
    rw [if_pos c1, if_neg c2, if_pos c1]
  · by_cases c2 : qA = pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
    · rw [if_neg c1, if_pos c2, if_pos c2]
    · rw [if_neg c1, if_neg c2, if_neg c2, if_neg c1]

theorem PairCtx.TT_data_heq (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    HEq (P.opJT con hj).output.data (P.swap.opJT hj con).output.data :=
  heq_recon (P.TT_skel con hj) _ _ (P.TT_data_tree con hj) (P.TT_data_couple con hj)

theorem corePosition_cast {S S' : Garden w} (hs : S = S') (D : ReconstructionData S) (D' : ReconstructionData S')
    (hD : HEq D D') (b : GBranch S.tree) (b' : GBranch S'.tree) (h : b.1 = b'.1) :
    D.corePosition b = D'.corePosition b' := by
  subst hs
  cases hD
  have : b = b' := Subtype.ext h
  subst this
  rfl

end WaveTurbulence.Stage1
