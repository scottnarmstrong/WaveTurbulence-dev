/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLDartEquiv
public import WaveTurbulence.Foundations.Molecule.CLBranchSigns
import Mathlib.Tactic

/-! # Mate and orientation commutation for the actual CL dart bijection -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSplicedDartEquiv_out (x : GardenDart (clSplicedGardenOfSlots hB hCL D)) :
    (contractGroup G.molecule S).out (clSplicedDartEquiv hB hCL D x) =
      (clSplicedGardenOfSlots hB hCL D).molecule.out x := by
  rcases x with ⟨c,side⟩ | l
  · cases side
    · change decide (G.sign (clSplicedBranchNameEquiv hB hCL D c.1).1.toNode = 1) =
        decide ((clSplicedGardenOfSlots hB hCL D).sign c.1.toNode = 1)
      exact congrArg (fun z : ℤˣ => decide (z = 1)) (clSplicedBranchName_sign hB hCL D c.1).symm
    · change decide (G.sign (clSplicedBranchNameEquiv hB hCL D c.1).1.toNode ≠ 1) =
        decide ((clSplicedGardenOfSlots hB hCL D).sign c.1.toNode ≠ 1)
      exact congrArg (fun z : ℤˣ => decide (z ≠ 1)) (clSplicedBranchName_sign hB hCL D c.1).symm
  · change decide (G.sign (clSplicedLeafNameEquiv hB hCL D l.1).1.toNode ≠ 1) =
      decide ((clSplicedGardenOfSlots hB hCL D).sign l.1.toNode ≠ 1)
    exact congrArg (fun z : ℤˣ => decide (z ≠ 1)) (clSplicedLeafName_sign hB hCL D l.1).symm

theorem clSplicedDartEquiv_mate (x : GardenDart (clSplicedGardenOfSlots hB hCL D)) :
    (contractGroup G.molecule S).mate (clSplicedDartEquiv hB hCL D x) =
      clSplicedDartEquiv hB hCL D ((clSplicedGardenOfSlots hB hCL D).molecule.mate x) := by
  rcases x with ⟨c,side⟩ | l
  · cases side <;> rfl
  · apply Subtype.ext
    apply congrArg Sum.inr
    apply Subtype.ext
    change G.pair (clLPLeafEquiv hB hCL D l).1.1 = _
    rw [clLPLeafEquiv_name,clLPLeafEquiv_name,clSplicedLeafName_pair]

end WaveTurbulence.Mole
