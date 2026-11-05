/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFamilyExtensionality

/-! # Data carried through two finite-family operations -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w} {ι : Type*}

/-- The active site's placement is exactly the source reverse placement. -/
theorem CoreFamily.nextPlacement_self (F : CoreFamily G ι) (i : ι) :
    F.nextPlacement i i = reversePlacement G (F.placement i) := by
  unfold CoreFamily.nextPlacement
  exact dite_eq_left rfl

/-- A distinct site's placement is the one derived from the separated source pair. -/
theorem CoreFamily.nextPlacement_other (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) :
    F.nextPlacement i j = (F.pairData i j hij).next := by
  unfold CoreFamily.nextPlacement
  exact dite_eq_right (Ne.symm hij)

/-- Actual branch transport through two finite-family operations. -/
@[expose] noncomputable def CoreFamily.doubleBranch (F : CoreFamily G ι) (i j : ι) (b : GBranch G.tree) :=
  coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j)
    (coreBranchEquiv G (F.placement i) b)

/-- Actual leaf transport through two finite-family operations. -/
@[expose] noncomputable def CoreFamily.doubleLeaf (F : CoreFamily G ι) (i j : ι) (l : GLeaf G.tree) :=
  coreLeafEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j)
    (coreLeafEquiv G (F.placement i) l)

/-- The double family branch transport is the proved separated-pair transport. -/
theorem CoreFamily.doubleBranch_pair (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) (b : GBranch G.tree) :
    (F.doubleBranch i j b).1 = ((F.pairData i j hij).branches b).1 :=
  congrArg (fun R => (coreBranchEquiv (unitTwistGarden G (F.placement i)) R
    (coreBranchEquiv G (F.placement i) b)).1) (F.nextPlacement_other hij)

/-- The double family leaf transport is the proved separated-pair transport. -/
theorem CoreFamily.doubleLeaf_pair (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) (l : GLeaf G.tree) :
    (F.doubleLeaf i j l).1 = ((F.pairData i j hij).leaves l).1 :=
  congrArg (fun R => (coreLeafEquiv (unitTwistGarden G (F.placement i)) R
    (coreLeafEquiv G (F.placement i) l)).1) (F.nextPlacement_other hij)

/-- Every atom set follows the composite actual branch transport. -/
theorem CoreFamily.double_atoms (F : CoreFamily G ι) (i j k : ι) :
    (((F.twist i).twist j).atoms k).image Subtype.val =
      (F.atoms k).image (fun b => (F.doubleBranch i j b).1) := by
  change (((F.atoms k).image (coreBranchEquiv G (F.placement i))).image
    (coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j))).image Subtype.val = _
  exact (Finset.image_image (s := (F.atoms k).image (coreBranchEquiv G (F.placement i)))
    (f := coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j)) (g := Subtype.val)).trans
      (Finset.image_image (s := F.atoms k) (f := coreBranchEquiv G (F.placement i))
        (g := fun b => (coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) b).1))

/-- Every designated lower follows the composite actual branch transport. -/
theorem CoreFamily.double_lower (F : CoreFamily G ι) (i j k : ι) :
    (((F.twist i).twist j).placement k).lower.1 = (F.doubleBranch i j (F.placement k).lower).1 := by
  have h₀ := (F.twist i).nextPlacement_lower j k
  have h₁ := F.nextPlacement_lower i k
  exact (congrArg Subtype.val h₀).trans (congrArg (fun b =>
    (coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) b).1) h₁)

/-- Every designated retained leaf follows the composite actual leaf transport. -/
theorem CoreFamily.double_retained (F : CoreFamily G ι) (i j k : ι) :
    (((F.twist i).twist j).placement k).retained.1 = (F.doubleLeaf i j (F.placement k).retained).1 := by
  have h₀ := (F.twist i).nextPlacement_retained j k
  have h₁ := F.nextPlacement_retained i k
  exact (congrArg Subtype.val h₀).trans (congrArg (fun l =>
    (coreLeafEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) l).1) h₁)

/-- Every designated slot is unchanged through two family operations. -/
theorem CoreFamily.double_keep (F : CoreFamily G ι) (i j k : ι) :
    (((F.twist i).twist j).placement k).keep = (F.placement k).keep :=
  ((F.twist i).nextPlacement_keep j k).trans (F.nextPlacement_keep i k)

/-- The actual double garden is the literal separated-pair garden. -/
theorem CoreFamily.double_garden (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) :
    unitTwistGarden (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) = (F.pairData i j hij).garden :=
  congrArg (unitTwistGarden (unitTwistGarden G (F.placement i))) (F.nextPlacement_other hij)

end WaveTurbulence.Twist
