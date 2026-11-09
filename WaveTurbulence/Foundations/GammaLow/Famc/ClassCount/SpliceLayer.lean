/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.SpliceLayer` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.LayerCnt.LayerRange
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.SpliceLayer
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Layout
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: a branch pre-layering of the skeleton induces one on the spliced garden

For a branch pre-layering `f` of `S`, `f ∘ ob` is a branch pre-layering of `G_sb = stSt γ S σ` (TARGET L1958): layers do not
increase from a unit representative to the atoms of the unit (`layer_le_upper`), and `ob` intertwines parents up to `repC`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- B1b (Mk-general form of `layer_le_repC`). -/
theorem layer_le_repCMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) (v : GBranch S.tree) {Mk : Set (CLVineG γ _)} :
    f v ≤ f (repC (stSt γ (Mk := Mk) S σ).cls v) := by
  by_cases h : ∃ u ∈ Fama.unitBlocks γ (Mk := Mk) S σ, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := h
    rw [Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hv]
    exact layer_le_upper S u.isBlock u.cl hf v hv
  · push_neg at h
    rw [Fama.stSt_repC_noneMk (Mk := Mk) hM σ h]

theorem layer_le_repC (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) (v : GBranch S.tree) :
    f v ≤ f (repC (stSt γ S σ).cls v) := layer_le_repCMk (Mk := ∅) S hM σ hf v

/-- B1b (Mk-general form of `ob_prelayering`). -/
theorem ob_prelayeringMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) {Mk : Set (CLVineG γ _)} :
    LFTwist.IsBranchPrelayering (stSt γ (Mk := Mk) S σ).G (f ∘ (stSt γ (Mk := Mk) S σ).M.ob) := by
  intro b c i hc
  have hn : c.1.2 ≠ [] := by
    have := congrArg (fun x : GNode (stSt γ (Mk := Mk) S σ).G.tree => x.1.2) hc
    simp [GBranch.toNode, GBranch.child] at this
    rw [this]; simp
  have hpar : GNode.parent c.toNode hn = b := by
    apply Subtype.ext
    have := congrArg (fun x : GNode (stSt γ (Mk := Mk) S σ).G.tree => x.1) hc
    simp [GBranch.toNode, GBranch.child] at this
    change (c.1.1, c.1.2.dropLast) = b.1
    rw [this]
    simp
  have ho : ((stSt γ (Mk := Mk) S σ).M.ob c).1.2 ≠ [] := fun h => hn (((stSt γ (Mk := Mk) S σ).M.ob_root c).1 h)
  have h1 := (stSt γ (Mk := Mk) S σ).M.ob_parent c hn ho
  rw [hpar] at h1
  simp only [Function.comp]
  rw [h1]
  have h2 : f ((stSt γ (Mk := Mk) S σ).M.ob c) ≤ f (GNode.parent ((stSt γ (Mk := Mk) S σ).M.ob c).toNode ho) := by
    have := hf (GNode.parent ((stSt γ (Mk := Mk) S σ).M.ob c).toNode ho) ((stSt γ (Mk := Mk) S σ).M.ob c)
      (((stSt γ (Mk := Mk) S σ).M.ob c).1.2.getLast ho)
    refine this ?_
    exact (Mole.parent_child_eq_node ((stSt γ (Mk := Mk) S σ).M.ob c).toNode ho).symm
  exact h2.trans (layer_le_repCMk (Mk := Mk) S hM σ hf _)

/-- `f ∘ ob` is a branch pre-layering of the spliced garden. -/
theorem ob_prelayering (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) :
    LFTwist.IsBranchPrelayering (stSt γ S σ).G (f ∘ (stSt γ S σ).M.ob) := ob_prelayeringMk (Mk := ∅) S hM σ hf

end WaveTurbulence.GammaLow.Famc.ClassCount
