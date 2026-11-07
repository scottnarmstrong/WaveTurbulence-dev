/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LayerExt
import Mathlib.Tactic

/-!
# The normalization of an LF output is the base (K1)

For an LF construction `h : LFConstruction s ε`, collapsing the reinserted regular tree and couple
of `h.output` gives back `s.base ε`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool)

theorem baseData_tree_lower : (s.baseData ε).tree (s.branches ε s.placement.lower) = .nil :=
  (transportReconstruction_tree s.plain (s.chosen_plain ε) (s.branches ε)
    (chosenLeafEquiv s.skeleton s.placement ε) (chosenLeafEquiv_pair s.skeleton s.placement ε)
    (normalizedData s.data s.placement.lower s.exceptional) s.placement.lower).trans
    (s.data.eraseTree_at s.placement.lower)

theorem baseData_couple_exc : (s.baseData ε).couple (s.pairs ε s.exceptional) = .triv :=
  (transportReconstruction_couple s.plain (s.chosen_plain ε) (s.branches ε)
    (chosenLeafEquiv s.skeleton s.placement ε) (chosenLeafEquiv_pair s.skeleton s.placement ε)
    (normalizedData s.data s.placement.lower s.exceptional) s.exceptional).trans
    ((s.data.eraseTree s.placement.lower).eraseCouple_at s.exceptional)

variable {s ε}

theorem eraseTree_final (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true) :
    (s.finalData ε X Q hX hQ).eraseTree (s.branches ε s.placement.lower) = s.midData ε Q hQ := by
  apply ReconstructionData.ext_tree_couple
  · funext c
    by_cases hc : c = s.branches ε s.placement.lower
    · subst c
      exact (ReconstructionData.eraseTree_at _ _).trans (baseData_tree_lower s ε).symm
    · exact ((ReconstructionData.eraseTree_other _ _ _ hc).trans (Function.update_of_ne hc _ _))
  · rfl

theorem eraseCouple_mid (Q : RegCpl) (hQ : Q.wf = true) :
    (s.midData ε Q hQ).eraseCouple (s.pairs ε s.exceptional) = s.baseData ε := by
  apply ReconstructionData.ext_tree_couple
  · rfl
  · funext q
    by_cases hq : q = s.pairs ε s.exceptional
    · subst q
      exact (ReconstructionData.eraseCouple_at _ _).trans (baseData_couple_exc s ε).symm
    · exact (ReconstructionData.eraseCouple_other _ _ _ hq).trans (Function.update_of_ne hq _ _)

/-- The layered garden after the couple (but not the tree) reinsertion. -/
@[expose] noncomputable def midLayered (h : LFConstruction s ε) : LayeredGarden w :=
  layeredReconstruction (s.midData ε h.newCouple h.couple_wf) (s.chosen_plain ε) h.midLayer h.mid_isLayering

theorem collapse_output_eq_mid (h : LFConstruction s ε) :
    collapsePairedTreeLayered h.output
      (h.data.decoded_chain_isSubPairedTree (s.chosen_plain ε) h.decodes (s.branches ε s.placement.lower)) =
      midLayered h := by
  refine collapse_insert_tree' h.data (s.chosen_plain ε) h.output (midLayered h) h.decodes _
    (s.midData ε h.newCouple h.couple_wf) (eraseTree_final _ _ _ _) h.newTree (Function.update_self _ _ _)
    ((s.midData ε h.newCouple h.couple_wf).garden_decodes _) h.treeInsertion.oldEmbedding
    h.treeInsertion.outside

theorem data_couple_exc (h : LFConstruction s ε) :
    h.data.couple (s.pairs ε s.exceptional) = h.newCouple :=
  Function.update_self _ _ _

/-- **K1.** Collapsing the reinserted tree and couple of an LF output gives back the base. -/
theorem normalized_output (h : LFConstruction s ε) :
    normalizedLayered h.output h.data (s.chosen_plain ε) h.decodes (s.branches ε s.placement.lower)
      (s.pairs ε s.exceptional) p = s.base ε := by
  classical
  have hT := collapse_output_eq_mid h
  have hcM : CanonicalObject p kind (midLayered h) := h.coupleInsertion.canonical (s.base_canonical ε)
  have hcB := s.base_canonical ε
  by_cases hq : h.data.couple (s.pairs ε s.exceptional) = .triv
  · have hQ : h.newCouple = .triv := (data_couple_exc h).symm.trans hq
    unfold normalizedLayered
    dsimp only
    rw [if_pos hq, hT]
    have hmd : s.midData ε h.newCouple h.couple_wf = s.baseData ε := by
      apply ReconstructionData.ext_tree_couple
      · rfl
      · funext q
        by_cases hqq : q = s.pairs ε s.exceptional
        · subst q
          exact (Function.update_self _ _ _).trans (hQ.trans (baseData_couple_exc s ε).symm)
        · exact Function.update_of_ne hqq _ _
    have hgar : (midLayered h).garden = (s.base ε).garden := by
      have h1 : (s.midData ε h.newCouple h.couple_wf).Decodes (s.chosen_plain ε) (midLayered h).garden :=
        (s.midData ε h.newCouple h.couple_wf).garden_decodes _
      have h2 := s.base_decodes ε
      rw [hmd] at h1
      exact rawOfGarden_injective_plain h1.1 h2.1 (h1.2.symm.trans h2.2)
    exact layered_eq_of_canonical_outAgree p hcM.criterion hcB.criterion hcM.plain hcB.plain hgar
      h.coupleInsertion.outside h.coupleInsertion.oldEmbedding
  · unfold normalizedLayered
    dsimp only
    rw [if_neg hq]
    have hED : h.data.eraseTree (s.branches ε s.placement.lower) = s.midData ε h.newCouple h.couple_wf :=
      eraseTree_final _ _ _ _
    have hFt : (h.data.eraseTree (s.branches ε s.placement.lower)).tree = (s.baseData ε).tree := by
      rw [hED]
      rfl
    have hT' : (midLayered h) = collapsePairedTreeLayered h.output
        (h.data.decoded_chain_isSubPairedTree (s.chosen_plain ε) h.decodes (s.branches ε s.placement.lower)) :=
      hT.symm
    refine collapse_insert_couple _ (s.chosen_plain ε) _ (s.base ε) _ _ ?_ ?_ p ?_ hcB.criterion ?_ ?_
    · exact hq
    · rw [hED, eraseCouple_mid]
      exact s.base_decodes ε
    · rw [hT]
      exact hcM.criterion
    · rw [hFt]
      exact h.coupleInsertion.oldEmbedding
    · rw [hFt, hT]
      exact h.coupleInsertion.outside

end WaveTurbulence.Stage1
