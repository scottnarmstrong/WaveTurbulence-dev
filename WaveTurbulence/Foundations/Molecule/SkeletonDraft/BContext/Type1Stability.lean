/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.FrameStability
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.RegStruct.Type1Frames


/-! # Unchanged side blocks in the type-1 B-step induction -/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- A node in the red component is separated from both other component frames. -/
theorem red_node_separation (c : MiniCplCode) (r : RegCpl) (a b target : Fin w × Path)
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes r (redFrame c a b).1 (redFrame c a b).2) :
    (IncompAddr target (greenFrame a b).1 ∧ IncompAddr target (greenFrame a b).2) ∧
      (IncompAddr target (blueFrame c a b).1 ∧ IncompAddr target (blueFrame c a b).2) :=
  ⟨(red_green_apart c hab).of_node r target ht,(red_blue_apart c hab).of_node r target ht⟩

/-- A node in the green component is separated from red and blue. -/
theorem green_node_separation (c : MiniCplCode) (g : RegCpl) (a b target : Fin w × Path)
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes g (greenFrame a b).1 (greenFrame a b).2) :
    (IncompAddr target (redFrame c a b).1 ∧ IncompAddr target (redFrame c a b).2) ∧
      (IncompAddr target (blueFrame c a b).1 ∧ IncompAddr target (blueFrame c a b).2) :=
  ⟨(red_green_apart c hab).symm.of_node g target ht,(green_blue_apart c hab).of_node g target ht⟩

/-- A node in the blue component is separated from red and green. -/
theorem blue_node_separation (c : MiniCplCode) (d : RegCpl) (a b target : Fin w × Path)
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes d (blueFrame c a b).1 (blueFrame c a b).2) :
    (IncompAddr target (redFrame c a b).1 ∧ IncompAddr target (redFrame c a b).2) ∧
      (IncompAddr target (greenFrame a b).1 ∧ IncompAddr target (greenFrame a b).2) :=
  ⟨(red_blue_apart c hab).symm.of_node d target ht,(green_blue_apart c hab).symm.of_node d target ht⟩

/-- The red input frame has precisely the source positive/negative root roles. -/
theorem red_frame_signs (σ : Fin w → ℤˣ) (c : MiniCplCode) (a b : Fin w × Path)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1) :
    nodeSign σ (redFrame c a b).1 = 1 ∧ nodeSign σ (redFrame c a b).2 = -1 := by
  constructor
  · rw [nodeSign_step,ha]
    rfl
  · rw [nodeSign_step,slotSign_partner,hb]
    rfl

/-- The green input frame reverses the two original trees and their middle signs. -/
theorem green_frame_signs (σ : Fin w → ℤˣ) (a b : Fin w × Path)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1) :
    nodeSign σ (greenFrame a b).1 = 1 ∧ nodeSign σ (greenFrame a b).2 = -1 := by
  constructor
  · simp only [nodeSign_step,hb,slotSign,ite_true,neg_neg]
  · simp only [nodeSign_step,ha,slotSign,ite_true]

/-- The blue input frame has the source positive/negative root roles. -/
theorem blue_frame_signs (σ : Fin w → ℤˣ) (c : MiniCplCode) (a b : Fin w × Path)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1) :
    nodeSign σ (blueFrame c a b).1 = 1 ∧ nodeSign σ (blueFrame c a b).2 = -1 := by
  constructor
  · rw [nodeSign_step,ha]
    rfl
  · rw [nodeSign_step,slotSign_partner,hb]
    rfl

end WaveTurbulence.Reg.Skeleton.BContext
