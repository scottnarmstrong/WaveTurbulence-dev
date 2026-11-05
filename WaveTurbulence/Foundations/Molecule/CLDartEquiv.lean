/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLPCChildren
public import WaveTurbulence.Foundations.Molecule.CLLPLeaves
public import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

/-! # The actual half-edge bijection for CL contraction
TARGET `block_clcn` (2). Both PC sides are retained together, and LP
leaves use the literal old pairing transported to the new forest.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))

@[expose] def pcDartRebracketEquiv :
    SurvivingPCChild G S × Bool ≃
      {p : ({c : GBranch G.tree // c.1.2 ≠ []} × Bool) // ¬ G.molecule.InGroup S (.inl p)} where
  toFun p := ⟨(p.1.1,p.2),fun hi => p.1.2 ((pc_internal_bool_iff (G := G) (S := S) p.1.1 p.2).mp hi)⟩
  invFun p := (⟨p.1.1,fun hi => p.2 ((pc_internal_bool_iff (G := G) (S := S) p.1.1 p.1.2).mpr hi)⟩,p.1.2)
  left_inv p := by
    obtain ⟨c,b⟩ := p
    apply congrArg (fun c => (c,b))
    exact Subtype.ext rfl
  right_inv p := Subtype.ext rfl

variable {G S} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

/-- Exact new darts versus old darts whose bonds are not internal to the block. -/
@[expose] noncomputable def clSplicedDartEquiv :
    GardenDart (clSplicedGardenOfSlots hB hCL D) ≃ ContractDart G.molecule S :=
  (Equiv.sumCongr
    (((clPCChildEquiv hB hCL D).prodCongr (Equiv.refl Bool)).trans (pcDartRebracketEquiv G S))
    (clLPLeafEquiv hB hCL D)).trans
      (Equiv.subtypeSum (p := fun x : GardenDart G => ¬ G.molecule.InGroup S x)).symm

theorem clSplicedDartEquiv_pc
    (c : {c : GBranch (clSplicedGardenOfSlots hB hCL D).tree // c.1.2 ≠ []}) (side : Bool) :
    (clSplicedDartEquiv hB hCL D (.inl (c,side))).1 =
      .inl ((clPCChildEquiv hB hCL D c).1,side) := rfl

theorem clSplicedDartEquiv_lp (l : GardenLPLeaf (clSplicedGardenOfSlots hB hCL D)) :
    (clSplicedDartEquiv hB hCL D (.inr l)).1 = .inr (clLPLeafEquiv hB hCL D l).1 := rfl

theorem clPCChildEquiv_name
    (c : {c : GBranch (clSplicedGardenOfSlots hB hCL D).tree // c.1.2 ≠ []}) :
    (clPCChildEquiv hB hCL D c).1.1 = (clSplicedBranchNameEquiv hB hCL D c.1).1 := rfl

theorem clLPLeafEquiv_name (l : GardenLPLeaf (clSplicedGardenOfSlots hB hCL D)) :
    (clLPLeafEquiv hB hCL D l).1.1 = (clSplicedLeafNameEquiv hB hCL D l.1).1 := rfl

end WaveTurbulence.Mole
