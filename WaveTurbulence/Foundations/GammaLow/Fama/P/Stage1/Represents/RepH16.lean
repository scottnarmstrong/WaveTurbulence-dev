/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepH16` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepH15
public import WaveTurbulence.Foundations.Stage1.Represents.RepH16
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS, VINE-D (16): countable sums of representations

`RepIntC.tsum`: if `val i` has a countable superposition by spliced kernels of `π` with weight mass `≤ B i` for every `i`
of a countable index set and `Σ B i < ∞`, then `Σ' val i` has one with mass `≤ Σ' B i` (the spliced kernels are uniformly
bounded under the amplitude bounds, `norm_splicedKernel_le`).  This sums the per-mode representations of INTERFACE v2.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set WaveTurbulence.GammaLow.FinalCount
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

variable {P : WTParams} {R : ℕ} {π : Stage1PieceG P R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem RepIntC.tsum (hS : π.Gsb.IsPlain) (hL : 0 < P.L) {ι : Type} [Countable ι] (val : ι → ℂ) (B : ι → ℝ)
    (hBs : Summable B) (h : ∀ i, RepIntC π tt base roots (val i) (B i)) :
    Summable val ∧ RepIntC π tt base roots (∑' i, val i) (∑' i, B i) := by
  choose Ξ hc w ctr edge hinge freq a1 a2 a3 a4 a5 using h
  have : ∀ i, Countable (Ξ i) := hc
  have hK0 : 0 ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) := by positivity
  have hkb : ∀ p : Σ i, Ξ i, ‖splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2) (hinge p.1 p.2)
      (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) := fun p =>
    norm_splicedKernel_le π.Gsb hS _ (a5 p.1 p.2) P.L hL _ _ _ _ _
  generalize ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) = K at hK0 hkb
  have hWs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2‖ := by
    refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun i => a3 i, ?_⟩
    exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs
  have hWKs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2 * splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hWs.mul_right K)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb p) (norm_nonneg _)
  have hsumval : ∑' p : Σ i, Ξ i, w p.1 p.2 * splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots = ∑' i, val i := by
    rw [hWKs.of_norm.tsum_sigma' (fun i => hWKs.of_norm.sigma_factor i)]
    exact tsum_congr fun i => (a2 i).symm
  have hvs : Summable val := (hWKs.of_norm.sigma).congr fun i => (a2 i).symm
  refine ⟨hvs, Σ i, Ξ i, inferInstance, fun p => w p.1 p.2, fun p => ctr p.1 p.2, fun p => edge p.1 p.2,
    fun p => hinge p.1 p.2, fun p => freq p.1 p.2, hWKs, hsumval.symm, hWs, ?_, fun p => a5 p.1 p.2⟩
  rw [hWs.tsum_sigma' (fun i => a3 i)]
  exact Summable.tsum_le_tsum a4 (Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs)
    hBs

end WaveTurbulence.GammaLow.Fama.Represents
