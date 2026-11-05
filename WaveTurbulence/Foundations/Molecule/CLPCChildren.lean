/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchNames
import Mathlib.Tactic

/-! # Bijection of the actual surviving parent-child bonds under CL splicing -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)

include hB hCL in
theorem cl_pc_survives_iff (c : GBranch G.tree) (hn : c.1.2 ≠ []) :
    ¬ G.molecule.InGroup S (.inl (⟨c,hn⟩,false)) ↔ c ∉ S ∨ c = a := by
  classical
  constructor
  · intro hi
    by_cases hc : c ∈ S
    · right
      have hp : ¬ InternalParent G S c := by
        rintro ⟨hn',hp⟩
        exact hi ⟨hc,hp⟩
      exact (block_one_region_root G hB hCL.1 hCL.2 c).mp ⟨hc,hp⟩
    · exact Or.inl hc
  · rintro (hc | hc) hi
    · exact hc hi.1
    · exact hCL.1 (hc ▸ (show InternalParent G S c from ⟨hn,hi.2⟩))

theorem pc_internal_bool_iff (c : {c : GBranch G.tree // c.1.2 ≠ []}) (side : Bool) :
    G.molecule.InGroup S (.inl (c,side)) ↔ G.molecule.InGroup S (.inl (c,false)) := by
  cases side
  · rfl
  · exact and_comm

/-- Child names of the surviving old PC bonds. -/
abbrev SurvivingPCChild (G : Garden w) (S : Finset (GBranch G.tree)) :=
  {c : {c : GBranch G.tree // c.1.2 ≠ []} // ¬ G.molecule.InGroup S (.inl (c,false))}

variable (D : CLSpliceSlots G S a b)

/-- First transport the nonroot condition along the actual branch-name bijection. -/
@[expose] noncomputable def clNonrootBranchNameEquiv :
    {c : GBranch (clSplicedGardenOfSlots hB hCL D).tree // c.1.2 ≠ []} ≃
      {c : {v : GBranch G.tree // v ∉ S ∨ v = a} // c.1.1.2 ≠ []} :=
  (clSplicedBranchNameEquiv hB hCL D).subtypeEquiv
    (fun c => (not_congr (clSplicedBranchName_root_iff hB hCL D c)).symm)

/-- Rebracket the old child typing data, using the proved external-PC characterization. -/
@[expose] def clOldPCChildEquiv :
    {c : {v : GBranch G.tree // v ∉ S ∨ v = a} // c.1.1.2 ≠ []} ≃ SurvivingPCChild G S where
  toFun c := ⟨⟨c.1.1,c.2⟩,(cl_pc_survives_iff hB hCL c.1.1 c.2).mpr c.1.2⟩
  invFun c := ⟨⟨c.1.1,(cl_pc_survives_iff hB hCL c.1.1 c.1.2).mp c.2⟩,c.1.2⟩
  left_inv c := by apply Subtype.ext; exact Subtype.ext rfl
  right_inv c := by apply Subtype.ext; exact Subtype.ext rfl

/-- The actual new PC children are bijective with exactly the surviving old PC bonds. -/
@[expose] noncomputable def clPCChildEquiv :
    {c : GBranch (clSplicedGardenOfSlots hB hCL D).tree // c.1.2 ≠ []} ≃ SurvivingPCChild G S :=
  (clNonrootBranchNameEquiv hB hCL D).trans (clOldPCChildEquiv hB hCL)

end WaveTurbulence.Mole
