/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotCpl
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum3
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed

/-! # STAGE1W-O4: the weighted tree slot target (row O4c)

`tree_slot_targetW`: the frontier-weighted native tree kernel `treeLeavesTop p g a` (weight layer `a`: the clock layer,
or the root layer when the root is a garden root) is a superposition on the clock box `timeBoxGt q q'`, with main's
slot mass times `cψ ^ treeExp`.  Nil chains: one root multiplier.  Incoherent chains: the staged INC-TOP tree clause at
the weight layer, extended to the closure of its box by time continuity, then the clock is frozen.  Coherent chains:
COH-TRUNK's `rowTopAgreementTree`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Reg WaveTurbulence.PL2330

/-- The nodes of a regular tree that can carry a frontier factor for the weight layer `a`. -/
def treeNodes (LG : LayeredGarden 1) (a : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun x => x.1.2 ≠ [] ∨ a ≠ LG.layer (GNode.root LG.garden.tree 0)

/-- The frontier exponent of a tree slot. -/
def treeExp (LG : LayeredGarden 1) (a : ℕ) : ℕ := (treeNodes LG a).card

end WaveTurbulence.Flower.Stage1WNoVine
