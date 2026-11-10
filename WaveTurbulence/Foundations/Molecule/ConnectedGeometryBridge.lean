/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CurrentBlockBridge
public import WaveTurbulence.Foundations.Molecule.BlockGeometricDichotomy

/-!
# CLCN C-1 integration on the current connected B2 blocks

The accepted induced-molecule connectedness is equivalent to the current
B2 in-group path relation once the group is nonempty. Current source
blocks therefore produce the accepted CLCN geometric witnesses directly.
-/

public section
namespace WaveTurbulence.Molecpl
open Finset TTree
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Current B2 connectedness gives the accepted induced-molecule connectedness. -/
theorem connected_to_induced {S : Finset V} (hne : S.Nonempty) (h : M.GroupConnected S) :
    Mole.GroupConnected M S := by
  refine ⟨hne,?_⟩
  intro u hu v hv
  apply Relation.EqvGen.mono _ u v (h u hu v hv)
  intro a b hab
  obtain ⟨x,hx,hxa,hxb⟩ := hab
  exact ⟨⟨x,hx⟩,hxa,hxb⟩

/-- The accepted CLCN block segment is constructed from a current B2 block. -/
@[expose] def currentBlockSegment {w : ℕ} (G : Garden w)
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b) :
    Mole.GardenBlockSegment G where
  atoms := S
  leftJoint := a
  rightJoint := b
  block := hB
  connected := connected_to_induced G.molecule ⟨a,hB.2.1⟩ hB.2.2.2.2.2.2.2.2.2

end WaveTurbulence.Molecpl
