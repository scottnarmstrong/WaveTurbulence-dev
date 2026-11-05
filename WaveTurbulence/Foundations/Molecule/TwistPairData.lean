/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPortPermutation

/-! # Source data for two core vines in a twist family -/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Two designated source core vines with at most one shared atom. -/
structure CorePairData {w : ℕ} (G : Garden w) (P Q : CorePlacement G) where
  left : Finset (GBranch G.tree)
  right : Finset (GBranch G.tree)
  upperLeft : GBranch G.tree
  upperRight : GBranch G.tree
  blockLeft : G.molecule.IsBlock left upperLeft P.lower
  clLeft : Mole.CLParentPattern G left upperLeft P.lower
  atLeft : IsPlacementAt G left P.lower P
  blockRight : G.molecule.IsBlock right upperRight Q.lower
  clRight : Mole.CLParentPattern G right upperRight Q.lower
  atRight : IsPlacementAt G right Q.lower Q
  separated : SeparatedGroups left right

variable {w : ℕ} {G : Garden w} {P Q : CorePlacement G}

/-- Reversing the order of the two source family members. -/
@[expose] def CorePairData.swap (D : CorePairData G P Q) : CorePairData G Q P where
  left := D.right
  right := D.left
  upperLeft := D.upperRight
  upperRight := D.upperLeft
  blockLeft := D.blockRight
  clLeft := D.clRight
  atLeft := D.atRight
  blockRight := D.blockLeft
  clRight := D.clLeft
  atRight := D.atLeft
  separated := fun x hx hy y hyx hyy => D.separated x hy hx y hyy hyx

/-- The actual second placement after the first unit twist. -/
@[expose] noncomputable def CorePairData.next (D : CorePairData G P Q) : CorePlacement (unitTwistGarden G P) :=
  otherPlacement G P Q D.blockLeft D.clLeft D.atLeft D.blockRight D.clRight D.atRight D.separated

/-- Both original lower atoms are distinct. -/
theorem CorePairData.lower_ne (D : CorePairData G P Q) : P.lower ≠ Q.lower :=
  separated_lower_ne G P Q D.blockLeft D.clLeft D.blockRight D.clRight D.separated

/-- Another source core vine stays core under this family member's unit twist. -/
theorem CorePairData.core_preserved (D : CorePairData G P Q) {X : VineType}
    (hcore : IsCoreCLVine G X D.right D.upperRight Q.lower) :
    IsCoreCLVine (unitTwistGarden G P) X (twistedAtoms G P D.right)
      (coreBranchEquiv G P D.upperRight) (coreBranchEquiv G P Q.lower) := by
  have hV := isVine_twistedAtoms G P hcore.1
  have hCL := clParentPattern_twist_separated G P Q D.blockLeft D.clLeft D.atLeft
    D.blockRight D.clRight D.separated
  have hat := otherPlacement_at G P Q D.blockLeft D.clLeft D.atLeft D.blockRight D.clRight D.atRight D.separated
  refine ⟨hV,hCL,?_⟩
  rcases hcore.2.2 with hx | ⟨hx,_⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hx,not_typeIIE_of_placement (unitTwistGarden G P) D.next hV.1 hCL hat⟩

/-- Two actual unit twists in the specified order. -/
@[expose] noncomputable def CorePairData.garden (D : CorePairData G P Q) : Garden w :=
  unitTwistGarden (unitTwistGarden G P) D.next

/-- Actual branching-node transport through both surgeries. -/
@[expose] noncomputable def CorePairData.branches (D : CorePairData G P Q) : GBranch G.tree ≃ GBranch D.garden.tree :=
  (coreBranchEquiv G P).trans (coreBranchEquiv (unitTwistGarden G P) D.next)

/-- Actual leaf transport through both surgeries. -/
@[expose] noncomputable def CorePairData.leaves (D : CorePairData G P Q) : GLeaf G.tree ≃ GLeaf D.garden.tree :=
  (coreLeafEquiv G P).trans (coreLeafEquiv (unitTwistGarden G P) D.next)

/-- Actual half-edge transport through both surgeries. -/
@[expose] noncomputable def CorePairData.darts (D : CorePairData G P Q) : GardenDart G ≃ GardenDart D.garden :=
  (twistDartEquiv G P).trans (twistDartEquiv (unitTwistGarden G P) D.next)

/-- Atom incidence commutes with the two actual surgeries. -/
theorem CorePairData.atom (D : CorePairData G P Q) (x : GardenDart G) :
    D.garden.molecule.atom (D.darts x) = D.branches (G.molecule.atom x) := by
  exact (twistDartEquiv_atom (unitTwistGarden G P) D.next (twistDartEquiv G P x)).trans
    (congrArg (coreBranchEquiv (unitTwistGarden G P) D.next) (twistDartEquiv_atom G P x))

/-- The mate involution commutes with the two actual surgeries. -/
theorem CorePairData.mate (D : CorePairData G P Q) (x : GardenDart G) :
    D.garden.molecule.mate (D.darts x) = D.darts (G.molecule.mate x) := by
  exact (twistDartEquiv_mate (unitTwistGarden G P) D.next (twistDartEquiv G P x)).trans
    (congrArg (twistDartEquiv (unitTwistGarden G P) D.next) (twistDartEquiv_mate G P x))

end WaveTurbulence.Twist
