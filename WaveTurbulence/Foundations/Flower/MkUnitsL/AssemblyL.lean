/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.HingeL
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAssembly

/-! # MK-UNITS-L (B3-2): the weighted vine case at a marking with per-unit top filters, at one parameter record

`vineCaseRepresentsFWMkL_of_gate` (B3's `vineCaseRepresentsFWMk_of_gate` with per-unit top filters): main's
`representsIntA_of_vineModes` applied to the producer piece at `mkAt mkF (repPt π)`, with the class sum
`class_sum_modesWMkL` (list-T4), the units' hinge data `unit_hinge_dataWMkL` (V5W-2L's `V5FrontierClassBoundAtL`,
list-T5), and B3's counting lemmas.  The top filter mass `topFilterMass ^ |SU j|` of unit `j` sits in its unit mass
and in its leaf factor; the size is `cψ ^ (16 N) · topFilterMass ^ (∑ⱼ |SU j|) · s`.

* `ChFWL`, `CvineFWL`: the constants (Stage1WVine's `ChFW`, `CvineFW` with `ChinFWL` and no filter mass).
* `unitTopFilters_transport`: the unit top filters along an equality of marked sets.

Adapted from `Flower/MkUnits/WAssembly.lean`, `Flower/Stage1WVine/WAssembly.lean` (constants) (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA.PrescribedPrimeGarden
open scoped ENNReal Classical

/-- The hinge constant of the weighted units with per-unit top filters (the filter masses sit in the unit masses). -/
def ChFWL (d : ℕ) (η : ℝ) : ℝ := max 1 (ChinFWL d η)

section VineCase
variable (Pg : WTParams) (C : ℝ)

end VineCase

end WaveTurbulence.Flower.MkUnitsL
