/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TwistAttachments

/-! # Both literal skeleton choices in the full LF construction

This is the structural candidate, before imposing the source coherent layer
patterns and combined layer-p count. Both original and twisted skeletons are
allowed; every nondesignated replacement code is transported unchanged.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

@[expose] noncomputable def chosenSkeleton : Bool → Garden w
  | false => G
  | true => unitTwistGarden G P

@[expose] noncomputable def chosenBranchEquiv (ε : Bool) :
    GBranch G.tree ≃ GBranch (chosenSkeleton G P ε).tree := by
  cases ε
  · exact Equiv.refl _
  · exact coreBranchEquiv G P

@[expose] noncomputable def chosenLeafEquiv (ε : Bool) :
    GLeaf G.tree ≃ GLeaf (chosenSkeleton G P ε).tree := by
  cases ε
  · exact Equiv.refl _
  · exact coreLeafEquiv G P

theorem chosenSkeleton_plain (hG : G.IsPlain) (ε : Bool) : (chosenSkeleton G P ε).IsPlain := by
  cases ε
  · exact hG
  · exact unitTwistGarden_plain G P hG

theorem chosenLeafEquiv_pair (ε : Bool) (l : GLeaf G.tree) :
    chosenLeafEquiv G P ε (G.pair l) = (chosenSkeleton G P ε).pair (chosenLeafEquiv G P ε l) := by
  cases ε
  · rfl
  · exact (unitTwistGarden_pair G P l).symm

@[expose] noncomputable def chosenPairEquiv (hG : G.IsPlain) (ε : Bool) :
    SourcePair G ≃ SourcePair (chosenSkeleton G P ε) :=
  sourcePairEquiv hG (chosenSkeleton_plain G P hG ε) (chosenLeafEquiv G P ε)
    (chosenLeafEquiv_pair G P ε)

/-- Actual structural reconstruction with precisely the two exceptional slots changed. -/
@[expose] noncomputable def lfReconstructionChoice (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) : ReconstructionData (chosenSkeleton G P ε) :=
  updateExceptional
    (transportReconstruction hG (chosenSkeleton_plain G P hG ε)
      (chosenBranchEquiv G P ε) (chosenLeafEquiv G P ε) (chosenLeafEquiv_pair G P ε) D)
    (chosenBranchEquiv G P ε P.lower)
    (chosenPairEquiv G P hG ε (pairOfLeaf G hG P.retained)) X Q hX hQ

theorem lfReconstructionChoice_tree_at (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) :
    (lfReconstructionChoice G P hG D ε X Q hX hQ).tree
      (chosenBranchEquiv G P ε P.lower) = X := by
  simp only [lfReconstructionChoice, updateExceptional, ReconstructionData.withCouple,
    ReconstructionData.withTree, Function.update_self]

theorem lfReconstructionChoice_couple_at (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) :
    (lfReconstructionChoice G P hG D ε X Q hX hQ).couple
      (chosenPairEquiv G P hG ε (pairOfLeaf G hG P.retained)) = Q := by
  simp only [lfReconstructionChoice, updateExceptional, ReconstructionData.withCouple,
    ReconstructionData.withTree, Function.update_self]

theorem lfReconstructionChoice_tree_other (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) (c : GBranch G.tree) (hc : c ≠ P.lower) :
    (lfReconstructionChoice G P hG D ε X Q hX hQ).tree (chosenBranchEquiv G P ε c) = D.tree c := by
  exact (updateExceptional_tree_other _ _ _ _ _ _ _ _
    (fun he => hc ((chosenBranchEquiv G P ε).injective he))).trans
      (transportReconstruction_tree _ _ _ _ _ D c)

theorem lfReconstructionChoice_couple_other (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) (r : SourcePair G)
    (hr : r ≠ pairOfLeaf G hG P.retained) :
    (lfReconstructionChoice G P hG D ε X Q hX hQ).couple (chosenPairEquiv G P hG ε r) = D.couple r := by
  exact (updateExceptional_couple_other _ _ _ _ _ _ _ _
    (fun he => hr ((chosenPairEquiv G P hG ε).injective he))).trans
      (transportReconstruction_couple _ _ _ _ _ D r)

/-- The exact combined-order constraint preserves the order of the actual
reconstructed garden for either skeleton choice. -/
theorem lfReconstructionChoice_order (hG : G.IsPlain)
    (D : ReconstructionData G) (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true)
    (hn : X.size + Q.size = (D.tree P.lower).size + (D.couple (pairOfLeaf G hG P.retained)).size) :
    ((lfReconstructionChoice G P hG D ε X Q hX hQ).garden (chosenSkeleton_plain G P hG ε)).order =
      (D.garden hG).order :=
  reconstructed_order_transport_update hG (chosenSkeleton_plain G P hG ε)
    (chosenBranchEquiv G P ε) (chosenLeafEquiv G P ε) (chosenLeafEquiv_pair G P ε)
    D P.lower (pairOfLeaf G hG P.retained) X Q hX hQ hn

end WaveTurbulence.LFTwist
