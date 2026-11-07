/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot2
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: layers and parent layers at the attachment positions of a reconstruction
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed

variable {w : ℕ} {S : Garden w}

/-- The layer of a clock source: `p` for the exterior root times, the layer of the core branch otherwise. -/
def clkLayer (p : ℕ) (layer0 : GBranch S.tree → ℕ) : ClkSrc S → ℕ
  | .inl _ => p
  | .inr b => layer0 b

theorem parentLayer_inflated (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ) (ν : GNode S.tree)
    (ν' : GNode (layeredReconstruction D hS layer hLayer).garden.tree)
    (hν' : ν'.1 = inflatedPosition S D.tree ν) :
    (layeredReconstruction D hS layer hLayer).parentLayer p ν' =
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (clkOfNode S ν) := by
  by_cases h : ν.1.2 = []
  · have h1 : ν = GNode.root S.tree ν.1.1 := Subtype.ext (Prod.ext rfl h)
    have h2 : clkOfNode S ν = .inl ν.1.1 := by
      unfold clkOfNode nodeToSlot; simp [h]
    have h3 : ν'.1.2 = [] := by
      rw [hν', h1, inflatedPosition_root]
    rw [h2]
    unfold LayeredGarden.parentLayer
    simp [h3, clkLayer]
  · obtain ⟨b, i, rfl⟩ : ∃ (b : GBranch S.tree) (i : Fin 3), ν = b.child i :=
      ⟨_, _, (child_parent ν h).symm⟩
    have h2 : clkOfNode S (b.child i) = .inr b := by
      unfold clkOfNode; rw [nodeToSlot_child]
    rw [h2]
    have h3 : ν'.1 = addrExt (D.corePosition b) [i] := by
      rw [hν', D.core_child_position]
    have h4 : ν'.1.2 ≠ [] := by
      rw [h3]; simp [addrExt]
    unfold LayeredGarden.parentLayer
    simp only [h4, ite_false, clkLayer]
    show layer ⟨(ν'.1.1, ν'.1.2.dropLast), _⟩ = layer (D.coreBranch hS b).toNode
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · show ν'.1.1 = (D.corePosition b).1
      rw [h3]; rfl
    · show ν'.1.2.dropLast = (D.corePosition b).2
      rw [h3]; simp [addrExt]

end WaveTurbulence.Represents
