/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepNoVine` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.Stage1.Represents.RepGlue
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS, vine-free case, step 1: no unit is spliced, so `G_sb = G_sk`

If `unitBlocks γ S σ = []` (no SG vine chain in `𝒱₀`), then `stSt γ S σ` is the trivial splice `SpState.init S`:
`G_sb = S`, no hinges, the old-name maps are the identity, the inherited pre-layering is the pre-layering.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `stSt_eq_init_of_unitBlocks_empty`). -/
theorem stSt_eq_init_of_unitBlocks_emptyMk (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = []) :
    stSt γ (Mk := Mk) S σ = SpState.init S := by
  unfold stSt; rw [h]; rfl


/-- B1b (Mk-general form of `stSt_G_eq_of_unitBlocks_empty`). -/
theorem stSt_G_eq_of_unitBlocks_emptyMk (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = []) :
    (stSt γ (Mk := Mk) S σ).G = S := by
  rw [stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h]; rfl

/-- `G_sb = G_sk` when no unit is spliced. -/
theorem stSt_G_eq_of_unitBlocks_empty (σ : Prescription S) (h : unitBlocks γ S σ = []) :
    (stSt γ S σ).G = S := stSt_G_eq_of_unitBlocks_emptyMk (Mk := ∅) σ h

/-- B1b (Mk-general form of `stSt_hinges_eq_empty`). -/
theorem stSt_hinges_eq_emptyMk (σ : Prescription S) {Mk : Set (CLVineG γ _)} (h : unitBlocks γ (Mk := Mk) S σ = []) :
    (stSt γ (Mk := Mk) S σ).hinges = ∅ := by
  classical
  ext c
  simp only [SpState.mem_hinges, Finset.notMem_empty, iff_false, not_not]
  have hs := stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h
  have : ∀ st : SpState S, st = SpState.init S → ∀ c : GBranch st.G.tree, st.cls (st.M.ob c) = none := by
    rintro st rfl c; rfl
  exact this _ hs c

/-- No hinges when no unit is spliced. -/
theorem stSt_hinges_eq_empty (σ : Prescription S) (h : unitBlocks γ S σ = []) :
    (stSt γ S σ).hinges = ∅ := stSt_hinges_eq_emptyMk (Mk := ∅) σ h

end WaveTurbulence.GammaLow.Fama.Represents
