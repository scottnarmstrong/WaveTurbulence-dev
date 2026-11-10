/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST
public import WaveTurbulence.Foundations.FlowerTop.Port.TypeFamilyST
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! AMEND-ST (R61 X4): Stage 1 pieces with STUBS, as a generalization of `Stage1Interface`.

`Stage1PieceDST` extends `Stage1PieceD` by the stub set `stubs` of the spliced garden; `RepresentsIntST` is
`RepresentsInt` with the stub time `ts` (the spliced kernels are `splicedKernelST`, stubs held at `ts`);
`RepresentsST` adds the garden-side identity with the stub kernel (`LeafFamily.valueSelFix`, FlowerP1Stub, adopted
verbatim) and the anchored leaf family; `Stage1PieceDST.Sound` adds `stub_pendant` (`StubPendant`): the stubs lie
in no hinge, selected object, maximal ladder or gap specification. With no stubs everything is the current data
(`Stage1PieceD.toST`, `RepresentsIntST.toOld`, `Sound.toST`, `Sound.toOld`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- Stub pendancy (R61: "stubs are pendant: never in a block, vine, ladder or regular object"), on the spliced
garden: the stubs are not hinges, lie in no selected object (`C.collection`), in no maximal ladder, and carry no
local gap specification. -/
def StubPendant {w : ℕ} (G : Garden w) (C : SourceVine.SubproChoices G)
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) (stubs : Finset (GBranch G.tree)) : Prop :=
  (∀ b ∈ stubs, b ∉ C.hinges) ∧ (∀ i, ∀ b ∈ stubs, b ∉ (C.collection i).atoms) ∧
    (∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ stubs, b ∉ S) ∧ (∀ b ∈ stubs, gs b = none)

/-- The part of `StubPendant` that does not involve the selected objects (hinges, ladders, gap specifications). -/
def StubPendantLadder {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree))
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) (stubs : Finset (GBranch G.tree)) : Prop :=
  (∀ b ∈ stubs, b ∉ hinges) ∧ (∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ stubs, b ∉ S) ∧
    (∀ b ∈ stubs, gs b = none)

theorem stubPendant_empty {w : ℕ} (G : Garden w) (C : SourceVine.SubproChoices G)
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) :
    StubPendant G C gs ∅ := by
  simp [StubPendant]

theorem stubPendantLadder_empty {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree))
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) :
    StubPendantLadder G hinges gs ∅ := by
  simp [StubPendantLadder]

end WaveTurbulence.LGSpine
