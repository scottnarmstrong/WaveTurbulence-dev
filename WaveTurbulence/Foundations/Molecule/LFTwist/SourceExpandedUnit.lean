/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.VineLayerGuards
public import WaveTurbulence.Foundations.Molecule.LFTwist.UnitCounts
public import WaveTurbulence.Foundations.Molecule.CoreVine

/-! # All source core-vine cases at the actual expanded unit-twist site

The printed type-I/no-extra-guard and type-II/minimum-rung-layer alternatives
supply the exact guard of the uniform cut-root proof. This covers the source
one-rung vine as well. Full LF reconstruction naturality is separate.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (P : CorePlacement S)

/-- Exactly the printed source layer eligibility alternatives. -/
@[expose] def SourceLayerEligible (X : VineType) (B : Finset (GBranch S.tree))
    (a : GBranch S.tree) : Prop :=
  X = .I ∨ X = .II ∧ ∃ R : Molecpl.EndRungData S.molecule B a P.lower,
    inducedPrelayer LG D hS hd P.lower ≤
      min (inducedPrelayer LG D hS hd R.left) (inducedPrelayer LG D hS hd R.right)

/-- The printed source assumptions imply the actual parent guard in every core case. -/
theorem sourceExpanded_parent_guard {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    inducedPrelayer LG D hS hd P.lower ≤
      inducedPrelayer LG D hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot) := by
  rcases helig with rfl | ⟨rfl,R,hR⟩
  · exact typeI_induced_parent_guard S P LG D hS hd hcore.1 hcore.2.1 hP
  · exact typeII_induced_parent_guard S P LG D hS hd hcore.1.1 R hP hR

/-- The actual expanded placement satisfies the cut-root proof's equal-layer condition. -/
theorem sourceExpanded_sameLowerLayer {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) {p : ℕ} (hc : LG.CanonCriterion p)
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    SameLowerLayer LG (expandedPlacement D hS hd P hq) :=
  expandedPlacement_sameLowerLayer LG D hS hd P hq hc
    (sourceExpanded_parent_guard LG D hS hd P hcore hP helig)

/-- Source core geometry supplies the original-tree condition used by G-class preservation. -/
theorem sourceExpanded_same_tree {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P) :
    (expandedPlacement D hS hd P hq).lower.1.1 =
      (LG.garden.pair (expandedPlacement D hS hd P hq).retained).1.1 :=
  expandedPlacement_same_tree LG D hS hd P hq
    (placement_same_tree P hcore.1.1 hcore.2.1 hP)

/-- The source all-cases canonicity step for the actual expanded unit surgery. -/
theorem sourceExpanded_unit_isCanonG {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) {p : ℕ} (hc : IsCanonG (p+1) LG)
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    IsCanonG (p+1) (unitLayerTwist LG (expandedPlacement D hS hd P hq)
      (sourceExpanded_sameLowerLayer LG D hS hd P hq hc.2.2.2 hcore hP helig)) :=
  (unitLayerTwist_isCanonG LG _ _ (sourceExpanded_same_tree LG D hS hd P hq hcore hP) p).mpr hc

/-- Canonical couples obey the identical source all-cases argument. -/
theorem sourceExpanded_unit_isCanonC {S : Garden 2} (LG : LayeredGarden 2) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (P : CorePlacement S)
    {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) {p : ℕ} (hc : IsCanonC (p+1) LG)
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    IsCanonC (p+1) (unitLayerTwist LG (expandedPlacement D hS hd P hq)
      (sourceExpanded_sameLowerLayer LG D hS hd P hq hc.2 hcore hP helig)) :=
  (unitLayerTwist_isCanonC _ _ p).mpr hc

end WaveTurbulence.LFTwist
