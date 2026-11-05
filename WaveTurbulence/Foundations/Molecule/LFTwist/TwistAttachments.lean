/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionOrder
public import WaveTurbulence.Foundations.Molecule.LFTwist.LayeredUnit

/-! # Actual attachment slots under a skeleton unit twist

Ordinary oriented pairs retain their positive and negative sides. Only the
exceptional pair may reverse sides, and LF replaces that slot freely.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (G : Garden w) (P : CorePlacement G) (hG : G.IsPlain)

/-- Exact oriented slot correspondence, including the exceptional pair. -/
@[expose] noncomputable def twistSourcePairEquiv : SourcePair G ≃ SourcePair (unitTwistGarden G P) :=
  sourcePairEquiv hG (unitTwistGarden_plain G P hG) (coreLeafEquiv G P)
    (fun l => (unitTwistGarden_pair G P l).symm)

/-- Branches and oriented pair slots reindex the entire actual assignment. -/
@[expose] noncomputable def twistReconstruction (D : ReconstructionData G) :
    ReconstructionData (unitTwistGarden G P) :=
  transportReconstruction hG (unitTwistGarden_plain G P hG)
    (coreBranchEquiv G P) (coreLeafEquiv G P) (fun l => (unitTwistGarden_pair G P l).symm) D

/-- Away from the exceptional pair, the positive endpoint's sign is unchanged. -/
theorem twist_pair_first_positive (q : SourcePair G)
    (hq : q ≠ pairOfLeaf G hG P.retained) :
    nodeSign (unitTwistGarden G P).sig (coreLeafEquiv G P (q.firstLeaf hG)).1 = 1 := by
  have hn : ¬ (q.firstLeaf hG = P.retained ∨ q.firstLeaf hG = G.pair P.retained) := by
    rintro (he | he)
    · apply hq
      exact (pairOfLeaf_firstLeaf G hG q).symm.trans (congrArg (pairOfLeaf G hG) he)
    · apply hq
      exact (pairOfLeaf_firstLeaf G hG q).symm.trans
        ((congrArg (pairOfLeaf G hG) he).trans (pairOfLeaf_partner G hG P.retained))
  have hs := coreLeafEquiv_sign G P (q.firstLeaf hG)
  change nodeSign G.sig (coreLeafEquiv G P (q.firstLeaf hG)).1 = 1
  apply hs.trans
  rw [coreLeafMultiplier, ite_eq_right hn, one_mul]
  exact sourcePair_first_sign G hG q

/-- The literal oriented endpoints of every unchanged couple slot are transported in order. -/
theorem twistSourcePair_sides (q : SourcePair G)
    (hq : q ≠ pairOfLeaf G hG P.retained) :
    ((twistSourcePairEquiv G P hG q).firstLeaf (unitTwistGarden_plain G P hG) =
      coreLeafEquiv G P (q.firstLeaf hG)) ∧
    ((twistSourcePairEquiv G P hG q).secondLeaf (unitTwistGarden_plain G P hG) =
      coreLeafEquiv G P (q.secondLeaf hG)) := by
  have hs := pairOfLeaf_sides_pos (unitTwistGarden G P) (unitTwistGarden_plain G P hG)
    (coreLeafEquiv G P (q.firstLeaf hG)) (twist_pair_first_positive G P hG q hq)
  have ho : G.pair (q.firstLeaf hG) = q.secondLeaf hG := by
    have hh := (pairOfLeaf_sides_pos G hG (q.firstLeaf hG) (sourcePair_first_sign G hG q)).2
    rw [pairOfLeaf_firstLeaf] at hh
    exact hh.symm
  exact ⟨hs.1, hs.2.trans ((unitTwistGarden_pair G P (q.firstLeaf hG)).trans
    (congrArg (coreLeafEquiv G P) ho))⟩

end WaveTurbulence.LFTwist
