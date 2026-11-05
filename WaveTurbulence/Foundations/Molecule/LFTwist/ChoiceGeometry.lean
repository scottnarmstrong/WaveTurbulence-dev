/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFConstruction

/-! # Exact code, sign, and original-tree bookkeeping for LF attachments -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed
namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

theorem placement_tree_index : s.placement.lower.1.1 = (s.skeleton.pair s.placement.retained).1.1 :=
  placement_same_tree s.placement s.core.1.1 s.core.2.1 s.selected

theorem branches_index (ε : Bool) (b : GBranch s.skeleton.tree) :
    (s.branches ε b).1.1 = b.1.1 := by
  cases ε
  · rfl
  · exact coreBranchEquiv_tree_index s.placement s.placement_tree_index b

theorem ordinary_branch_sign (ε : Bool) (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    nodeSign (s.chosen ε).sig (s.branches ε b).1 = nodeSign s.skeleton.sig b.1 := by
  cases ε
  · rfl
  · exact ordinaryBranchSign_twist _ _ b hb

theorem ordinary_pair_sides (ε : Bool) (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    ((s.pairs ε q).firstLeaf (s.chosen_plain ε) = chosenLeafEquiv s.skeleton s.placement ε (q.firstLeaf s.plain)) ∧
    ((s.pairs ε q).secondLeaf (s.chosen_plain ε) = chosenLeafEquiv s.skeleton s.placement ε (q.secondLeaf s.plain)) := by
  cases ε
  · have he : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    exact ⟨congrArg (fun r => r.firstLeaf s.plain) he,congrArg (fun r => r.secondLeaf s.plain) he⟩
  · exact twistSourcePair_sides _ _ _ q hq

theorem leaves_index (ε : Bool) (l : GLeaf s.skeleton.tree) :
    (chosenLeafEquiv s.skeleton s.placement ε l).1.1 = l.1.1 := by
  cases ε
  · rfl
  · exact coreLeafEquiv_tree_index s.placement s.placement_tree_index l

end LFSource
namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

theorem tree_other (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    h.data.tree (s.branches ε b) = s.data.tree b := by
  change (s.finalData ε h.newTree h.newCouple h.tree_wf h.couple_wf).tree _ = _
  rw [s.finalData_eq_choice ε h.newTree h.newCouple h.tree_wf h.couple_wf]
  exact lfReconstructionChoice_tree_other _ _ _ _ _ _ _ _ _ b hb

theorem couple_other (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    h.data.couple (s.pairs ε q) = s.data.couple q := by
  change (s.finalData ε h.newTree h.newCouple h.tree_wf h.couple_wf).couple _ = _
  rw [s.finalData_eq_choice ε h.newTree h.newCouple h.tree_wf h.couple_wf]
  exact lfReconstructionChoice_couple_other _ _ _ _ _ _ _ _ _ q hq

end LFConstruction

/-- The literal address of every native couple branch. -/
theorem coupleContextBranch_address {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (q : SourcePair S) (c : GBranch (decodedCouple (D.couple q)).tree) :
    (coupleContextBranch D hS q c).1 = addrExt (coupleRoot D hS q c.1.1) c.1.2 := by
  obtain ⟨⟨i,r⟩,hc⟩ := c
  fin_cases i <;> rfl

end WaveTurbulence.LFTwist
