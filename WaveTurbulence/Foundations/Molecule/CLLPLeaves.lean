/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLLeafNames
import Mathlib.Tactic

/-! # Bijection of actual LP leaves under CL splicing
TARGET `block_clcn` (2): exactly the noninternal old LP bonds survive.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ}

/-- The exact LP-dart leaf carrier used by GardenDart. -/
abbrev GardenLPLeaf (G : Garden w) :=
  {l : GLeaf G.tree // G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ []}

theorem internalLeaf_iff_lp_internal (G : Garden w) (S : Finset (GBranch G.tree)) (l : GardenLPLeaf G) :
    IsInternalLeaf G S l.1 ↔ G.molecule.InGroup S (.inr l) := by
  constructor
  · rintro ⟨hm,hn,hp,hi⟩
    exact hi
  · intro hi
    exact ⟨l.2.1,l.2.2.1,l.2.2.2,hi⟩

variable {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem cl_old_lp_retained_iff (l : GardenLPLeaf G) :
    IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D) l.1 ↔ ¬ G.molecule.InGroup S (.inr l) :=
  (clSignedBoundary_retained_iff hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle
    D.kept_ne_middle D.upper D.lower l.1).trans (not_congr (internalLeaf_iff_lp_internal G S l))

theorem cl_lp_profile_iff (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    ((clSplicedGardenOfSlots hB hCL D).mark l = none ∧ l.1.2 ≠ [] ∧
      ((clSplicedGardenOfSlots hB hCL D).pair l).1.2 ≠ []) ↔
    (G.mark (clSplicedLeafNameEquiv hB hCL D l).1 = none ∧
      (clSplicedLeafNameEquiv hB hCL D l).1.1.2 ≠ [] ∧
      (G.pair (clSplicedLeafNameEquiv hB hCL D l).1).1.2 ≠ []) := by
  have hroot := (not_congr (clSplicedLeafName_root_iff hB hCL D l)).symm
  have hpair := not_congr (clSplicedLeafName_root_iff hB hCL D ((clSplicedGardenOfSlots hB hCL D).pair l))
  have he := congrArg (fun k : GLeaf G.tree => k.1.2) (clSplicedLeafName_pair hB hCL D l)
  have hpair' : (G.pair (clSplicedLeafNameEquiv hB hCL D l).1).1.2 ≠ [] ↔
      ((clSplicedGardenOfSlots hB hCL D).pair l).1.2 ≠ [] := he ▸ hpair
  rw [clSplicedLeafName_mark]
  exact and_congr Iff.rfl (and_congr hroot hpair'.symm)

@[expose] def clOldLPLeafEquiv :
    {l : {l : GLeaf G.tree // IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D) l} //
      G.mark l.1 = none ∧ l.1.1.2 ≠ [] ∧ (G.pair l.1).1.2 ≠ []} ≃
    {l : GardenLPLeaf G // ¬ G.molecule.InGroup S (.inr l)} where
  toFun l := ⟨⟨l.1.1,l.2⟩,(cl_old_lp_retained_iff hB hCL D ⟨l.1.1,l.2⟩).mp l.1.2⟩
  invFun l := ⟨⟨l.1.1,(cl_old_lp_retained_iff hB hCL D l.1).mpr l.2⟩,l.1.2⟩
  left_inv l := by apply Subtype.ext; exact Subtype.ext rfl
  right_inv l := by apply Subtype.ext; exact Subtype.ext rfl

/-- The new LP-dart leaf carrier equals precisely the surviving old LP-dart carrier. -/
@[expose] noncomputable def clLPLeafEquiv : GardenLPLeaf (clSplicedGardenOfSlots hB hCL D) ≃
    {l : GardenLPLeaf G // ¬ G.molecule.InGroup S (.inr l)} :=
  ((clSplicedLeafNameEquiv hB hCL D).subtypeEquiv (cl_lp_profile_iff hB hCL D)).trans
    (clOldLPLeafEquiv hB hCL D)

end WaveTurbulence.Mole
