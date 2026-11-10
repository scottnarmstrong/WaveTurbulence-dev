/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVN3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.Stage1.Represents.RepMom2
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN3
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS, VINE-D: the sum over the outer slot modes

`repIntC_modes`: a countable weighted sum `Σ_ξ W_ξ val_ξ` of per-mode `RepIntC` representations (`repIntC_mode`) is a
`RepIntC` representation of mass `Bt` as soon as the weighted masses `Σ_ξ ‖W_ξ‖ B_ξ` are `≤ Bt` (computed in `ℝ≥0∞`, where
`tsum_modes_moment` pays the modulation losses).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

variable {P : WTParams} {R : ℕ} {π : Stage1PieceG P R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem repIntC_modes (hS : π.Gsb.IsPlain) (hL : 0 < P.L) {ι : Type} [Countable ι] (W : ι → ℂ) (val : ι → ℂ)
    (B : ι → ℝ) (hB0 : ∀ ξ, 0 ≤ B ξ) (h : ∀ ξ, RepIntC π tt base roots (val ξ) (B ξ)) (Bt : ℝ) (hBt : 0 ≤ Bt)
    (hsum : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≤ ENNReal.ofReal Bt) :
    RepIntC π tt base roots (∑' ξ, W ξ * val ξ) Bt := by
  have hne : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hs : Summable fun ξ => ‖W ξ‖ * B ξ :=
    (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hB0 ξ))
  obtain ⟨-, hr⟩ := RepIntC.tsum hS hL (fun ξ => W ξ * val ξ) (fun ξ => ‖W ξ‖ * B ξ) hs
    (fun ξ => (h ξ).smul (W ξ))
  refine hr.mono ?_
  have h1 : ENNReal.ofReal (∑' ξ, ‖W ξ‖ * B ξ) = ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) :=
    ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (hB0 ξ)) hs
  exact (ENNReal.ofReal_le_ofReal_iff hBt).1 (h1 ▸ hsum)


end WaveTurbulence.GammaLow.Fama.Represents
