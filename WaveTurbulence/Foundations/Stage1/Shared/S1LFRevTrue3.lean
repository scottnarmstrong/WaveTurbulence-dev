/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue2
import Mathlib.Tactic

/-!
# Reversal of a true-choice LF operation: reconstruction data of the reverse source
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

section Data
variable {s : LFSource p kind LG} (h : LFConstruction s true)

theorem normalizedData_output_true :
    normalizedData h.data (revSourceT s h).placement.lower (revSourceT s h).exceptional = s.baseData true := by
  show (h.data.eraseTree (s.branches true s.placement.lower)).eraseCouple
    (pairOfLeaf (unitTwistGarden s.skeleton s.placement) (unitTwistGarden_plain s.skeleton s.placement s.plain)
      (coreLeafEquiv s.skeleton s.placement s.placement.retained)) = s.baseData true
  rw [← pairs_true_exc s]
  have hED : h.data.eraseTree (s.branches true s.placement.lower) = s.midData true h.newCouple h.couple_wf :=
    eraseTree_final _ _ _ _
  rw [hED]
  exact eraseCouple_mid _ _

/-- The base data of the reverse source (choice `true`) is the original base data, up to the cast. -/
theorem revSourceT_baseData_heq :
    HEq ((revSourceT s h).baseData true) (s.baseData false) := by
  have A : (revSourceT s h).baseData true =
      transportReconstruction (unitTwistGarden_plain s.skeleton s.placement s.plain)
        ((revSourceT s h).chosen_plain true)
        (coreBranchEquiv _ (reversePlacement s.skeleton s.placement))
        (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
        (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm)
        (s.baseData true) :=
    congrArg (fun D => transportReconstruction (unitTwistGarden_plain s.skeleton s.placement s.plain)
        ((revSourceT s h).chosen_plain true)
        (coreBranchEquiv _ (reversePlacement s.skeleton s.placement))
        (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
        (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm) D)
      (normalizedData_output_true h)
  have B : s.baseData true = transportReconstruction s.plain (s.chosen_plain true)
      (coreBranchEquiv s.skeleton s.placement) (coreLeafEquiv s.skeleton s.placement)
      (fun l => (unitTwistGarden_pair s.skeleton s.placement l).symm) (s.baseData false) := by
    rw [LFSource.baseData_false]
    rfl
  refine HEq.trans (heq_of_eq A) ?_
  rw [B]
  exact transport_twice_heq s.plain (s.chosen_plain true) ((revSourceT s h).chosen_plain true)
    (coreBranchEquiv s.skeleton s.placement) (coreLeafEquiv s.skeleton s.placement)
    (fun l => (unitTwistGarden_pair s.skeleton s.placement l).symm)
    (coreBranchEquiv _ (reversePlacement s.skeleton s.placement))
    (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
    (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm)
    (unitTwistGarden_involutive s.skeleton s.placement)
    (coreBranchEquiv_twice_val s.skeleton s.placement) (coreLeafEquiv_twice_val s.skeleton s.placement) _

theorem cast_pair_val {K G : Garden w} (e : K = G) (q : SourcePair G) : (e ▸ q : SourcePair K).1 = q.1 := by
  subst e
  rfl

theorem revSourceT_pairs_val :
    ((revSourceT s h).pairs true (revSourceT s h).exceptional).1 = s.exceptional.1 := by
  have e : (revSourceT s h).exceptional = s.pairs true s.exceptional := (pairs_true_exc s).symm
  have hq := sourcePairEquiv_twice s.plain (s.chosen_plain true) ((revSourceT s h).chosen_plain true)
    (coreLeafEquiv s.skeleton s.placement) (fun l => (unitTwistGarden_pair s.skeleton s.placement l).symm)
    (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
    (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm)
    (unitTwistGarden_involutive s.skeleton s.placement) (coreLeafEquiv_twice_val s.skeleton s.placement)
    s.exceptional
  have h2 : (revSourceT s h).pairs true (revSourceT s h).exceptional =
      sourcePairEquiv (s.chosen_plain true) ((revSourceT s h).chosen_plain true)
        (coreLeafEquiv _ (reversePlacement s.skeleton s.placement))
        (fun l => (unitTwistGarden_pair _ (reversePlacement s.skeleton s.placement) l).symm)
        (s.pairs true s.exceptional) := by
    show _ = _
    rw [← e]
    rfl
  rw [h2]
  have := (congrArg Subtype.val hq).trans (cast_pair_val (unitTwistGarden_involutive s.skeleton s.placement) s.exceptional)
  exact this

theorem revSourceT_branches_val :
    ((revSourceT s h).branches true (revSourceT s h).placement.lower).1 = s.placement.lower.1 :=
  coreBranchEquiv_twice_val s.skeleton s.placement s.placement.lower

theorem revSourceT_midData_heq (Q : RegCpl) (hQ : Q.wf = true) :
    HEq ((revSourceT s h).midData true Q hQ) (s.midData false Q hQ) := by
  unfold LFSource.midData
  exact withCouple_heq (unitTwistGarden_involutive s.skeleton s.placement) (revSourceT_baseData_heq h)
    ((revSourceT_pairs_val h).trans (congrArg Subtype.val (LFSource.pairs_false s s.exceptional)).symm) Q hQ

theorem revSourceT_finalData_heq (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true) :
    HEq ((revSourceT s h).finalData true X Q hX hQ) (s.finalData false X Q hX hQ) := by
  unfold LFSource.finalData
  exact withTree_heq (unitTwistGarden_involutive s.skeleton s.placement) (revSourceT_midData_heq h Q hQ)
    (revSourceT_branches_val h) X hX

theorem revSourceT_finalData_data_heq :
    HEq ((revSourceT s h).finalData true (s.data.tree s.placement.lower) (s.data.couple s.exceptional)
      (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional)) s.data :=
  HEq.trans (revSourceT_finalData_heq h _ _ _ _) (heq_of_eq s.finalData_identity)

end Data

end WaveTurbulence.Stage1
