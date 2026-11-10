/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.ClassL
public import WaveTurbulence.Foundations.Flower.MkUnits.WClass

/-! # MK-UNITS-L (B3-2): the weighted class sum of a fine′ piece with per-unit top filters

* `unitHkFWL`: the weighted class kernel of a unit with the product filter `S : List ℝ`,
  `twistedRecenteredFWL p (g j₁) S … (modW λ)` (Stage1WVine's `unitHkFW`, which is `S = none`).
* `class_sum_modesWMkL`: B3's `class_sum_modesWMk` with the extra weight `E` presented by the unit top filters `SU` on
  every run-class member: the sum of the values over the fine′ output set is the outer mode sum of the representative's
  spliced garden with the unit factors `unitHkFWL P p (SU j)` (list-T4 through `weightedClassFactorization_depL`).

Adapted from `Flower/MkUnits/WClass.lean`, `Flower/Stage1WVine/WHinge1.lean` (`unitHkFW`) (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.VineEstS2 WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Flower.V5W2L (topFilterWeightL twistedRecenteredFWL)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-- **The weighted class kernel of a unit with a product of top filters** (`S = []`: Stage1WVine's `unitHkFW`). -/
def unitHkFWL (P : WTParams) (p : ℕ) (S : List ℝ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (g : Fin w → Mom P.d → ℂ) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun lam t k =>
  twistedRecenteredFWL p (g a.1.1) S G a
    (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
    P.L P.γ P.δ h wBar (VineC.modW (lam : ℝ)) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)

variable {p : ℕ}

end WaveTurbulence.Flower.MkUnitsL
