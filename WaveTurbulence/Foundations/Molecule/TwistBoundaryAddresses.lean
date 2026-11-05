/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSplicedForest
public import WaveTurbulence.Foundations.Molecule.BoundaryAddressAlgebra

/-! # The retained splice-boundary address diagram commutes with the actual twist

TARGET twistexplain (c,e). Whole retained subtrees move with their
relative addresses unchanged; the signed boundary slots remain canonical.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- Every relative address in a retained boundary subtree has the same spliced slot after twisting. -/
theorem unitTwist_boundary_address_append (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (i : Fin 3) (q : Path) :
    exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep
      (appendAddress ((originalSpliceBoundary G P hB hCL D).node i).1 q) =
      appendAddress ((twistedSpliceBoundary G P hB hCL hP D).node i).1 q := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have hb := excluded_lower_incomparable G P hB hCL D
  have hp := excluded_pair_incomparable G P hB hCL hP D
  have hk := spliceSlots_kept G P hP D
  have hs := clSameSign_unitTwist G P hB.2.2.2.1
  have hbase (j : Fin 3) :
      exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep
        (appendAddress ((Mole.clBaseBoundary (G := G) a P.lower D.excluded P.keep j).1) q) =
      appendAddress ((Mole.clBaseBoundary (G := unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
        D.excluded P.keep (Equiv.swap (1 : Fin 3) 2 j)).1) q := by
    fin_cases j
    · change exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep (appendAddress (a.child D.excluded).1 q) =
        appendAddress ((coreBranchEquiv G P a).child D.excluded).1 q
      have he := exchangeAddress_append_fixed P.lower.1 (G.pair P.retained).1 (a.child D.excluded).1 P.keep q
        (fun hi => ⟨fun h => hb.2 ⟨hi,h⟩,fun h => hb.1 ⟨hi.symm,h⟩⟩)
        (fun hi => ⟨fun h => hp.2 ⟨hi,h⟩,fun h => hp.1 ⟨hi.symm,h⟩⟩)
      apply he.trans
      apply congrArg (fun z => appendAddress z q)
      change (a.1.1,a.1.2 ++ [D.excluded]) =
        ((coreBranchEquiv G P a).1.1,(coreBranchEquiv G P a).1.2 ++ [D.excluded])
      rw [fa]
    · change exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep
        (appendAddress (P.lower.1.1,P.lower.1.2 ++ [1]) q) =
        appendAddress ((coreBranchEquiv G P P.lower).child (Mole.otherOuterChild P.keep)).1 q
      have he := exchangeAddress_lower_child P.lower.1 (G.pair P.retained).1 P.keep 1 q
      apply he.trans
      apply congrArg (fun z => appendAddress z q)
      change ((G.pair P.retained).1.1,(G.pair P.retained).1.2 ++ [freeSwap P.keep 1]) =
        ((coreBranchEquiv G P P.lower).1.1,(coreBranchEquiv G P P.lower).1.2 ++ [Mole.otherOuterChild P.keep])
      rw [coreBranchEquiv_lower_val,freeSwap_middle P.keep P.outer]
    · change exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep
        (appendAddress (P.lower.1.1,P.lower.1.2 ++ [Mole.otherOuterChild P.keep]) q) =
        appendAddress ((coreBranchEquiv G P P.lower).child 1).1 q
      have he := exchangeAddress_lower_child P.lower.1 (G.pair P.retained).1 P.keep (Mole.otherOuterChild P.keep) q
      apply he.trans
      apply congrArg (fun z => appendAddress z q)
      change ((G.pair P.retained).1.1,(G.pair P.retained).1.2 ++ [freeSwap P.keep (Mole.otherOuterChild P.keep)]) =
        ((coreBranchEquiv G P P.lower).1.1,(coreBranchEquiv G P P.lower).1.2 ++ [1])
      rw [coreBranchEquiv_lower_val,freeSwap_other P.keep P.outer]
  change exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep
      (appendAddress (Mole.clBaseBoundary (G := G) a P.lower D.excluded D.kept (Mole.clBoundarySelector D.excluded (Mole.clSameSign a P.lower) i)).1 q) =
    appendAddress (Mole.clBaseBoundary (G := unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
      D.excluded P.keep (Mole.clBoundarySelector D.excluded
        (Mole.clSameSign (G := unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)) i)).1 q
  rw [hk,hs,← clBoundarySelector_flip]
  exact hbase _

end WaveTurbulence.Twist
