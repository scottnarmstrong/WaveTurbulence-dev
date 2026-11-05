/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SpliceTransportComparison

/-! # Literal equality of the two source spliced forests -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The original accepted source CL-spliced garden with explicit justified slots. -/
@[expose] noncomputable def originalSplicedGarden (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (D : Mole.CLSpliceSlots G S a P.lower) : Garden w :=
  Mole.clSplicedGardenOfSlots hB hCL D

/-- The accepted source CL-spliced garden of the designated actual twist. -/
@[expose] noncomputable def twistedSplicedGarden (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) : Garden w :=
  Mole.clSplicedGardenOfSlots (isBlock_twistedAtoms G P hB)
    (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)

/-- The exact ordered forests of the two source spliced gardens are equal. -/
theorem unitTwist_splicedForest (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    (twistedSplicedGarden G P hB hCL hP D).tree = (originalSplicedGarden G P hB hCL D).tree := by
  change forestReplace (coreTwistForest G P) (coreBranchEquiv G P a).1
    (Mole.spliceCrown (unitTwistGarden G P) (twistedSpliceBoundary G P hB hCL hP D).node) =
      forestReplace G.tree a.1 (Mole.spliceCrown G (originalSpliceBoundary G P hB hCL D).node)
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have hc := unitTwist_spliceCrown G P hB hCL hP D
  exact (congrArg₂ (forestReplace (coreTwistForest G P)) fa hc).trans
    (coreTwistForest_outer_replace G P hB hCL hP _)

/-- Each actual ordered boundary subtree is equal, with its source slot index retained. -/
theorem unitTwist_boundarySubtree (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (i : Fin 3) :
    Mole.spliceNodeSubtree (unitTwistGarden G P) ((twistedSpliceBoundary G P hB hCL hP D).node i) =
      Mole.spliceNodeSubtree G ((originalSpliceBoundary G P hB hCL D).node i) := by
  have h := TTree.node.inj (unitTwist_spliceCrown G P hB hCL hP D)
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

end WaveTurbulence.Twist
