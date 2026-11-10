/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepNoVine5` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine4
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr8
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS: `RepresentsInt` of the vine-free Stage 1 piece `stage1PieceOf` (the case `𝒱_0 = ∅`)

For a regular reconstruction `D` of the skeleton `S` (with the original garden `LG = layeredReconstruction D ..`)
and a prescription `σ` with no spliced unit (`unitBlocks γ S σ = []`), the piece `stage1PieceOf` has
`G_sb = S`, no hinges, `b_sk = 0` and `g_sk = g_reg`, and its `RepresentsInt` is `represents_noVine_core`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed

variable {R : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `unitIngredients_noVine`). -/
theorem unitIngredients_noVineMk {S : Garden (2 * R)} (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = []) :
    unitIngredients γ (Mk := Mk) S σ = ∅ := by
  ext T
  simp [unitIngredients, h]


/-- B1b (Mk-general form of `bskOf_noVine`). -/
theorem bskOf_noVineMk {S : Garden (2 * R)} (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = []) :
    bskOf γ (Mk := Mk) S σ = 0 := by
  unfold bskOf
  rw [unitIngredients_noVineMk (Mk := Mk) σ h]
  simp

theorem bskOf_noVine {S : Garden (2 * R)} (σ : Prescription S) (h : unitBlocks γ S σ = []) :
    bskOf γ S σ = 0 := bskOf_noVineMk (Mk := ∅) σ h

/-- B1b (Mk-general form of `gskOf_noVine`). -/
theorem gskOf_noVineMk {S : Garden (2 * R)} (g : ℕ) (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = [])
    (l : GBranch S.tree → ℕ) : gskOf γ (Mk := Mk) g S σ l = g := by
  unfold gskOf
  have : (Set.toFinite (unitIngredients γ (Mk := Mk) S σ)).toFinset = ∅ := by
    ext T; simp [unitIngredients_noVineMk (Mk := Mk) σ h]
  rw [this]
  simp

theorem gskOf_noVine {S : Garden (2 * R)} (g : ℕ) (σ : Prescription S) (h : unitBlocks γ S σ = [])
    (l : GBranch S.tree → ℕ) : gskOf γ g S σ l = g := gskOf_noVineMk (Mk := ∅) g σ h l



end WaveTurbulence.GammaLow.Fama.Represents
