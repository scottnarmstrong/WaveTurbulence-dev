/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceUnitBlocks
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# B2c MK-SUBPRO: the survivors of a marked group and their original joint pairs

Data of the original garden `G` (no splice state), used by the marked-group branches of the gap specification
(ruling R171, o75 (2.3): the indicator `𝒵` has a factor for every group of `𝒞`, marked groups included) and of the
hinge pairs (o75 Theorem 7.5′(5), 75-F1).

* `groupSurvMk G Mk S`: the survivors of the group `S` (the chosen `MarkedGroupUnits`, the same choice as
  `groupUnitsMk` and `survivorsMk`); `[]` for an unmarked group.  `survivorsMk G σ Mk` is their concatenation over the
  SG groups (`survivorsMk_eq`).
* `SurvPairSpec G T j p`: `p` is an out/in pair of darts of `G` at `j`, both inside the atomic group `T` (a pair of the
  survivor `T` at its joint `j`).  `survOrigPair G T j` chooses one.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- **The survivors of the group `S`** (B2c): those of the chosen `MarkedGroupUnits` (`[]` if `S` is unmarked). -/
@[expose] noncomputable def groupSurvMk (G : Garden w) (Mk : Set (CLVine G)) (S : Finset (GBranch G.tree)) :
    List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if markedGroup G Mk S then (if h : Nonempty (MarkedGroupUnits G S Mk) then (Classical.choice h).surv else [])
    else []

theorem survivorsMk_eq (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) :
    survivorsMk G σ Mk = (sgGroups G σ).flatMap (groupSurvMk G Mk) := rfl

theorem groupSurvMk_empty (G : Garden w) (S : Finset (GBranch G.tree)) : groupSurvMk G ∅ S = [] := by
  simp [groupSurvMk, not_markedGroup_empty]

theorem groupSurvMk_of_not_marked {G : Garden w} {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (h : ¬ markedGroup G Mk S) : groupSurvMk G Mk S = [] := by
  simp [groupSurvMk, h]

/-- The survivors of a marked group are those of the chosen `MarkedGroupUnits`. -/
theorem groupSurvMk_of_marked {G : Garden w} {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (h : markedGroup G Mk S) (hn : Nonempty (MarkedGroupUnits G S Mk)) :
    groupSurvMk G Mk S = (Classical.choice hn).surv := by
  classical
  unfold groupSurvMk
  rw [if_pos h, dif_pos hn]

end WaveTurbulence.GammaLow.FinalCount.H
