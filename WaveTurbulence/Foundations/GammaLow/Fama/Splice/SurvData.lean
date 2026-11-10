/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData


/-!
# B2c MK-SUBPRO: the survivors of a marked group and their original joint pairs

Data of the original garden `G` (no splice state), used by the marked-group branches of the gap specification
(ruling R171, o75 (2.3): the indicator `𝒵` has a factor for every group of `𝒞`, marked groups included) and of the
hinge pairs (o75 Theorem 7.5′(5), 75-F1).

* `groupSurvMk γ G Mk S`: the survivors of the group `S` (the chosen `MarkedGroupUnits`, the same choice as
  `groupUnitsMk` and `survivorsMk`); `[]` for an unmarked group.  `survivorsMk γ G σ Mk` is their concatenation over the
  SG groups (`survivorsMk_eq`).
* `SurvPairSpec G T j p`: `p` is an out/in pair of darts of `G` at `j`, both inside the atomic group `T` (a pair of the
  survivor `T` at its joint `j`).  `survOrigPair G T j` chooses one.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- **The survivors of the group `S`** (B2c): those of the chosen `MarkedGroupUnits` (`[]` if `S` is unmarked). -/
@[expose] noncomputable def groupSurvMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (Mk : Set (CLVineG γ G)) (S : Finset (GBranch G.tree)) :
    List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if markedGroup γ G Mk S then (if h : Nonempty (MarkedGroupUnits γ G S Mk) then (Classical.choice h).surv else [])
    else []

theorem survivorsMk_eq (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) :
    survivorsMk γ G σ Mk = (sgGroups γ G σ).flatMap (groupSurvMk γ G Mk) := rfl

theorem groupSurvMk_empty (G : Garden w) (S : Finset (GBranch G.tree)) : groupSurvMk γ G ∅ S = [] := by
  simp [groupSurvMk, not_markedGroup_empty]

theorem groupSurvMk_of_not_marked {G : Garden w} {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)}
    (h : ¬ markedGroup γ G Mk S) : groupSurvMk γ G Mk S = [] := by
  simp [groupSurvMk, h]

/-- The survivors of a marked group are those of the chosen `MarkedGroupUnits`. -/
theorem groupSurvMk_of_marked {G : Garden w} {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)}
    (h : markedGroup γ G Mk S) (hn : Nonempty (MarkedGroupUnits γ G S Mk)) :
    groupSurvMk γ G Mk S = (Classical.choice hn).surv := by
  classical
  unfold groupSurvMk
  rw [if_pos h, dif_pos hn]

/-- **A pair of the survivor `T` at its joint `j`**: an out/in pair of darts of `G` at `j`, both inside `T`. -/
@[expose] def SurvPairSpec (G : Garden w) (T : Finset (GBranch G.tree)) (j : GBranch G.tree)
    (p : GardenDart G × GardenDart G) : Prop :=
  TripleAt G j p.1 p.2 ∧ G.molecule.InGroup T p.1 ∧ G.molecule.InGroup T p.2

/-- The chosen pair of the survivor `T` at `j` (`none` if there is none). -/
@[expose] noncomputable def survOrigPair (G : Garden w) (T : Finset (GBranch G.tree)) (j : GBranch G.tree) :
    Option (GardenDart G × GardenDart G) := by
  classical
  exact if h : ∃ p, SurvPairSpec G T j p then some h.choose else none

theorem survOrigPair_isSome {G : Garden w} {T : Finset (GBranch G.tree)} {j : GBranch G.tree}
    (h : ∃ p, SurvPairSpec G T j p) : ∃ p, survOrigPair G T j = some p ∧ SurvPairSpec G T j p := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold survOrigPair
  rw [dif_pos h]

end WaveTurbulence.GammaLow.Fama
