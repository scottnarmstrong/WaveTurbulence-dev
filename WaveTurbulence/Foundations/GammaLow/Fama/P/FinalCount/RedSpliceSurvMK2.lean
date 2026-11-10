/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRes4
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# B2a MK-RUNS: the chosen runs and survivors, and the residual decomposition of a survivor

* `markedUnitsOfMK γ h`: the `MarkedGroupUnits` chosen by `groupUnitsMk` for a marked group
  (`groupUnitsMk_of_markedMK`, `mem_survivorsMk_iffMK`);
* `groupUnitsMk_spineMK`, `unitBlocks_chainMK'`: every run is a spine of unmarked `𝒱`-ingredients;
* `Spine.aroundMK`: a block chain cut around one member is a `SkelDecomp`;
* `surv_sdecompMK`: **every survivor `t` of a marked SG group is decomposed (`SDecomp`) in the splice
  `stSt γ G σ Mk`** around the runs at its two joints, exactly as main's skipped ingredient is (`skip_sdecomp`): in the
  garden molecule, or (75-W1) in the adjoint of an HVC whose only survivor is `t`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

section generic
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



end generic

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The runs and survivors chosen for a marked group (those of `groupUnitsMk` and `survivorsMk`). -/
noncomputable def markedUnitsOfMK (γ : ℝ) [Fact (γ ≤ 1 / 2)] {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)} (h : markedGroup γ G Mk S) :
    MarkedGroupUnits γ G S Mk :=
  Classical.choice (exists_markedGroupUnits h)

/-- The units of a marked group are the chosen runs. -/
theorem groupUnitsMk_of_markedMK {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)} (h : markedGroup γ G Mk S) :
    groupUnitsMk γ G Mk S = (markedUnitsOfMK γ h).runs := by
  classical
  unfold groupUnitsMk
  simp only [h, exists_markedGroupUnits h, ↓reduceIte, ↓reduceDIte]
  rfl


section units
variable {σ : Prescription G} {Mk : Set (CLVineG γ G)}



end units

section sdecomp
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {σ : Prescription G} {Mk : Set (CLVineG γ G)}


end sdecomp

end WaveTurbulence.GammaLow.Fama
