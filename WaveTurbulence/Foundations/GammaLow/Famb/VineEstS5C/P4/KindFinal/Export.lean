/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFinal4
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Prefix
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.KindFinal.Reality
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.KindFinal.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Prefix
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecFinal4
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.KindFinal.Export` (sha256 c54527efe0362cb9…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # V5-KIND final export: the kind-generic VINEEST (R57)

* `vineEstCanonLayerC2MK_of_gates`, **`vineEstCanonLayerHalfMK_of_gates`**: `WTPrefix VineEstCanonLayerC2MK` / `WTPrefix
  VineEstCanonLayerHalfMK` (TARGET Proposition `vineest`, L1742–L1749, for every `kind : Bool`, i.e. G ∈ G_{p+1} (kind = true) or C_{p+1}
  (kind = false), over canonical objects), from W2's kind-generic certificate `W2.uniformTermCertK` (no hypotheses), PL234's
  `reality_all` (`P1.realityAll`) and the two original unweighted leafwise gates.
* The gates are the only hypotheses; main discharges them (`Spine.leafwise_coherent_approximation`, `Spine.leafwise_incoherent_decay`,
  Foundations/Spine/SourceProviders.lean), whose abbrev texts equal lg-spine-u's.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.KindFinal
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.KindFinal WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C

/-- **VINEEST (ii), kind-generic** (the statement consumed by S2's `stage1ReductionGate_of_V5` and main's `layergarden_v2_of_V5`):
`WTPrefix VineEstCanonLayerHalfMK` from the two leafwise gates. -/
theorem vineEstCanonLayerHalfMK_of_gatesΓ (hG : LeafwiseCoherentApproximationGate) (hI : LeafwiseIncoherentDecayGate) :
    WTPrefix (VineEstCanonLayerHalfMKΓ (γF := γF)) :=
  Final.vineEstCanonLayerHalfMK_of_uniformCertΓ W2.uniformTermCertKΓ hG hI P1.realityAll

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.KindFinal
