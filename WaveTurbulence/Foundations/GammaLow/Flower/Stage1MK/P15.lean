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
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportMK
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt

/-! # FLOWER-LOW (packet L8), item I (wave 15): marked Stage-1′ declarations over `𝒱_γ`

Item-I declarations of L8's sub-areas (I-BASE, I-GATE) portable after L5a-G's `Vine.Align` publication, and
declarations deferred from earlier waves, copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- In the stem-dependent case B2e's `markIX` is a fine marking (B2e handoff, field for field). -/
theorem fineMarking_markIXLow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (hS : StemDep σ kSel) (hfine : ∀ a : Fama.VineA.PrescribedPrimeGarden γF w, a.FineTransportedAt γF (markIXLow (γF := γF) J pat t s kSel)) :
    FineMarkingLow J pat t s kSel σ (markIXLow (γF := γF) J pat t s kSel) :=
  ⟨fun _ => Set.subset_union_left, fun _ _ _ c hc hun => Or.inr ⟨hc, hun⟩,
    fun _ _ hc => hc.imp id fun h => ⟨hS, h⟩, hfine⟩

end

end WaveTurbulence.GammaLow.Flower
