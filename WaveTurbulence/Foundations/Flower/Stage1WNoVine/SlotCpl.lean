/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotKer
public import WaveTurbulence.Foundations.Flower.Stage1W.TypeBound
public import WaveTurbulence.Foundations.Flower.CohTrunk.Main
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum2

/-! # STAGE1W-O4: the weighted couple slot target (row O4c)

`couple_slot_targetW`: the frontier-weighted native couple kernel `coupleLeavesTopR p g a b` (per-arm weights,
weight layers `a, b`: the clock layers, or the root layer at an arm whose root is a garden root) is a centred
superposition on the clock box `timeBox q q'`, with main's slot mass times `cψ ^ cplExp` (`cplExp` counts the nodes
that can carry a frontier factor).
- trivial couples: the weight is a product of two root multipliers (SNorm multiplier lemma);
- incoherent couples: the staged `TopIncoherentDecayAtR` (INC-TOP) at the weight layers, then the clocks of the
  garden-root arms are frozen (`coupleLeavesTopR_freeze0/1`);
- coherent couples: COH-TRUNK's `rowTopAgreementCoupleR` makes the weight a single multiplier. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Reg WaveTurbulence.PL2330

/-- The nodes of a regular couple that can carry a frontier factor for the weight layers `a, b`. -/
def cplNodes (LG : LayeredGarden 2) (a b : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun x => x.1.2 ≠ [] ∨ ![a, b] x.1.1 ≠ LG.layer (GNode.root LG.garden.tree x.1.1)

/-- The frontier exponent of a couple slot. -/
def cplExp (LG : LayeredGarden 2) (a b : ℕ) : ℕ := (cplNodes LG a b).card

end WaveTurbulence.Flower.Stage1WNoVine
