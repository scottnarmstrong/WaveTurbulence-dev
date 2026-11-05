/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFamilyDoubleTransport

/-! # The commuting involutions on actual gardens with their source family

TARGET Definition twist. These involutions are derived from the concrete
subtree surgeries, rather than supplied as abstract action hypotheses.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {ι : Type*}

/-- A source family step is an involution, including every transported vine. -/
theorem familyStep_involutive (i : ι) : Function.Involutive (familyStep (w := w) i) := by
  intro s
  obtain ⟨G,F⟩ := s
  have hb (b : GBranch G.tree) : (F.doubleBranch i i b).1 = b.1 :=
    (congrArg (fun R => (coreBranchEquiv (unitTwistGarden G (F.placement i)) R
      (coreBranchEquiv G (F.placement i) b)).1) (F.nextPlacement_self i)).trans
      (coreBranchEquiv_twice_val G (F.placement i) b)
  have hl (l : GLeaf G.tree) : (F.doubleLeaf i i l).1 = l.1 :=
    (congrArg (fun R => (coreLeafEquiv (unitTwistGarden G (F.placement i)) R
      (coreLeafEquiv G (F.placement i) l)).1) (F.nextPlacement_self i)).trans
      (coreLeafEquiv_twice_val G (F.placement i) l)
  apply familyState_ext
  · exact (congrArg (unitTwistGarden (unitTwistGarden G (F.placement i))) (F.nextPlacement_self i)).trans
      (unitTwistGarden_involutive G (F.placement i))
  · rfl
  · intro k
    exact (F.double_atoms i i k).trans (Finset.image_congr (fun b _ => hb b))
  · intro k
    exact hb (F.upper k)
  · intro k
    exact (F.double_lower i i k).trans (hb (F.placement k).lower)
  · intro k
    exact (F.double_retained i i k).trans (hl (F.placement k).retained)
  · intro k
    exact F.double_keep i i k

/-- Any two source family steps commute, including every transported vine. -/
theorem familyStep_commute (i j : ι) : Function.Commute (familyStep (w := w) i) (familyStep j) := by
  intro s
  obtain ⟨G,F⟩ := s
  by_cases hij : j = i
  · subst j
    rfl
  have hji := Ne.symm hij
  have hb (b : GBranch G.tree) : (F.doubleBranch j i b).1 = (F.doubleBranch i j b).1 :=
    (F.doubleBranch_pair hij b).trans
      (((F.pairData j i hij).branch_commute b).symm.trans (F.doubleBranch_pair hji b).symm)
  have hl (l : GLeaf G.tree) : (F.doubleLeaf j i l).1 = (F.doubleLeaf i j l).1 :=
    (F.doubleLeaf_pair hij l).trans
      (((F.pairData j i hij).leaf_commute l).symm.trans (F.doubleLeaf_pair hji l).symm)
  apply familyState_ext
  · exact (F.double_garden hij).trans
      (((F.pairData j i hij).garden_commute).trans (F.double_garden hji).symm)
  · rfl
  · intro k
    exact (F.double_atoms j i k).trans
      ((Finset.image_congr (fun b _ => hb b)).trans (F.double_atoms i j k).symm)
  · intro k
    exact hb (F.upper k)
  · intro k
    exact (F.double_lower j i k).trans ((hb (F.placement k).lower).trans (F.double_lower i j k).symm)
  · intro k
    exact (F.double_retained j i k).trans ((hl (F.placement k).retained).trans (F.double_retained i j k).symm)
  · intro k
    exact (F.double_keep j i k).trans (F.double_keep i j k).symm

end WaveTurbulence.Twist
