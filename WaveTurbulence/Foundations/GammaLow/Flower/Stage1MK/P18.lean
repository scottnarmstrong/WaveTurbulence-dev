/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P16
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P17
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Flower.MkSubpro.Piece
public import WaveTurbulence.Foundations.Flower.MkSubpro.Support
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Marking
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Zero
public import WaveTurbulence.Foundations.Stage1.ClassCount.Final
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproMeetBMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansAssembly
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansLayering
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansSkeleton

/-! # FLOWER-LOW (packet L8), item I (wave 18): the B4 layer of the marked Stage 1′ over `𝒱_γ`

The declarations on the path of main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s` (B4) not yet ported: L8's own (Stage1MKGate, MkSubpro,
Geometry *MK, Vine.A *MK) and the Stage-1 helpers that L6's H port has only at `Src.γL` (`FinalCount.S1Exists`,
`S1Overlap`, `S1Vinechain`, `S1Erase`, `S1Split`, `SubproObjMap`, `SubproGap2`, `AsmVN13`, `RedSpliceGapKind`), here
at the family `P.γ`/`γF`; copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.ClassCount
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- B2d: **the Stage 1′ class count at any marking** (TARGET L2241-L2252 for the pieces `stage1PieceOf … σ Mk`, runs
of the marked groups spliced), unconditional. -/
theorem classCountMkLow : ClassCountStmtMkLow (γF := γF) fun _ _ _ => True :=
  classCount_of_legsMkLow decodeSizeLeg (skeletonLegMk_of_codeLegMkLow skeletonCodeLegMkLow) layeringLegMkLow

end

end WaveTurbulence.GammaLow.Flower
