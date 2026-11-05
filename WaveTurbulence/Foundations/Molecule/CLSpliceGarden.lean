/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLRetainedPairing
public import WaveTurbulence.Foundations.Molecule.GardenLeafTransport
import Mathlib.Tactic

/-! # Constructing the actual CL-spliced garden
TARGET `block_clcn` (2). The old pairing is restricted to surviving leaves
and transported by the proved concrete leaf bijection; the three subtree
attachments and all their signs come from the proved CL joint slots.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Concrete child-slot choices justified by the CL incidence classification. -/
structure CLSpliceSlots (G : Garden w) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) where
  excluded : Fin 3
  kept : Fin 3
  excluded_ne_middle : excluded ≠ 1
  kept_ne_middle : kept ≠ 1
  upper : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ excluded
  lower : ∀ i : Fin 3, i.succ ∈ internalPositions G S b ↔ i = kept

/-- The slot data are obtained from the actual block, without further assumptions. -/
@[expose] noncomputable def clSpliceSlotsOfBlock (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) : CLSpliceSlots G S a b := by
  classical
  apply Classical.choice
  obtain ⟨i,hi,ha⟩ := no_parent_joint_excluded_child G hB.2.1 hB.2.2.2.2.1
    hB.2.2.2.2.2.1 hCL.1
  obtain ⟨j,hj,hb⟩ := with_parent_joint_retained_child G hB.2.2.1
    hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1 hCL.2
  exact ⟨⟨i,j,hi,hj,ha,hb⟩⟩

theorem CLSpliceSlots.excluded_missing (D : CLSpliceSlots G S a b) :
    D.excluded.succ ∉ internalPositions G S a := fun h => (D.upper D.excluded).mp h rfl

@[expose] noncomputable def clSpliceBoundary (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b) : SpliceBoundaryRoots G a :=
  clSignedBoundaryRoots hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle

/-- Construction with explicit, already-proved child-slot choices. -/
@[expose] noncomputable def clSplicedGardenOfSlots (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b) : Garden w :=
  gardenOfLeafTransport G (IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D))
    (clSignedBoundary_pair_closed hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle
      D.kept_ne_middle D.upper D.lower)
    (spliceLeafEquiv (clSpliceBoundary hB hCL D))
    (spliceLeafEquiv_sign (clSpliceBoundary hB hCL D)
      (clSignedBoundary_sign hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle D.kept_ne_middle))

/-- TARGET `block_clcn` (2): the actual spliced garden, defined for every CL block. -/
@[expose] noncomputable def clSplicedGarden (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) : Garden w :=
  clSplicedGardenOfSlots hB hCL (clSpliceSlotsOfBlock hB hCL)

theorem clSplicedGardenOfSlots_tree (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b) :
    (clSplicedGardenOfSlots hB hCL D).tree = spliceForest G a (clSpliceBoundary hB hCL D).node := rfl

theorem clSplicedGardenOfSlots_plain (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b) (hP : G.IsPlain) :
    (clSplicedGardenOfSlots hB hCL D).IsPlain := by
  intro l
  exact hP _

end WaveTurbulence.Mole
