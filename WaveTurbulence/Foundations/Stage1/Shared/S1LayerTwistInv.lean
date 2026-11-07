/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LayerExt
public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalCriterion
public import WaveTurbulence.Foundations.Molecule.TwistFamilyExtensionality
public import WaveTurbulence.Foundations.Molecule.UnitTwistInvolution
import Mathlib.Tactic

/-!
# The layered unit twist is an involution (reverse placement)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links WaveTurbulence.LFTwist

variable {w : ℕ}

theorem naiveNodeEquiv_twice_val (G : Garden w) (P : CorePlacement G) (n : GNode G.tree) :
    (naiveNodeEquiv (unitTwistGarden G P) (reversePlacement G P) (naiveNodeEquiv G P n)).1 = n.1 := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    have h1 := naiveNodeEquiv_branch G P b
    have h2 := naiveNodeEquiv_branch (unitTwistGarden G P) (reversePlacement G P) (coreBranchEquiv G P b)
    exact (congrArg (fun m => (naiveNodeEquiv (unitTwistGarden G P) (reversePlacement G P) m).1) h1).trans
      ((congrArg Subtype.val h2).trans (coreBranchEquiv_twice_val G P b))
  | inr l =>
    have h1 := naiveNodeEquiv_leaf G P l
    have h2 := naiveNodeEquiv_leaf (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l)
    exact (congrArg (fun m => (naiveNodeEquiv (unitTwistGarden G P) (reversePlacement G P) m).1) h1).trans
      ((congrArg Subtype.val h2).trans (coreLeafEquiv_twice_val G P l))

theorem unitLayerTwist_involutive (LG : LayeredGarden w) (P : CorePlacement LG.garden)
    (he : SameLowerLayer LG P)
    (he' : SameLowerLayer (unitLayerTwist LG P he) (reversePlacement LG.garden P)) :
    unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he' = LG := by
  have hg : (unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he').garden =
      LG.garden := unitTwistGarden_involutive LG.garden P
  apply layered_ext hg
  intro x
  by_cases hx : x.2 ∈ (LG.garden.tree x.1).nodes
  · let n : GNode LG.garden.tree := ⟨x, hx⟩
    let n2 := naiveNodeEquiv (unitTwistGarden LG.garden P) (reversePlacement LG.garden P)
      (naiveNodeEquiv LG.garden P n)
    have hv : n2.1 = x := naiveNodeEquiv_twice_val LG.garden P n
    have e1 : layerAt (unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he') x =
        (unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he').layer n2 := by
      rw [← hv]
      exact layerAt_node (unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he') n2
    rw [e1]
    exact (unitLayerTwist_node (unitLayerTwist LG P he) (reversePlacement LG.garden P) he'
      (naiveNodeEquiv LG.garden P n)).trans ((unitLayerTwist_node LG P he n).trans (layerAt_node LG n).symm)
  · have hx2 : x.2 ∉ ((unitLayerTwist (unitLayerTwist LG P he) (reversePlacement LG.garden P) he').garden.tree
        x.1).nodes := by
      rw [hg]
      exact hx
    unfold layerAt
    rw [dite_eq_right hx, dite_eq_right hx2]

end WaveTurbulence.Stage1
