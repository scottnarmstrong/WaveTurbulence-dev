/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.RootDef` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.ClassCount.Irregular
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
public import WaveTurbulence.Foundations.Stage1.ClassCount.BondSplit
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots3
public import WaveTurbulence.Foundations.Molecule.GardenDeficitBound
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.RootDef
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: degree deficits

* the degree deficit `Σ_v (4 - deg v)` of a molecule with disjoint ladders is at most `16 (#ladders) + 4 (#free atoms)`
  (interior ladder atoms have degree `4`);
* the root things of a plain garden (`rootThings`) are bounded by its degree deficit.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

namespace LadderFam
variable {M : Molecule V D} {ι : Type} (F : LadderFam M ι) (i : ι)

end LadderFam

section splice
variable {V' D' : Type} [DecidableEq V'] [Fintype D'] [DecidableEq D']

end splice

section garden
open WaveTurbulence.Reg.Skeleton TTree WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {S : Garden w}

end garden

section inst
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ}

/-- B2d: **the root things are bounded by `16 ρ̄`** at any marked set. -/
theorem rootThings_leMk (S : Garden w) (hS : S.IsPlain) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    rootThings hS ≤ 16 * ((stSt γ S σ Mk).G.molecule.rho + (Fama.unitBlocks γ S σ Mk).length) := by
  classical
  have hM := Mole.garden_isMolecule S
  have hM' := Mole.garden_isMolecule (stSt γ S σ Mk).G
  refine (rootThings_le_deficit hS).trans ?_
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    set SD := spliceDataOfMk γ S hM σ Mk v0 with hSD
    have hint : ∀ i, i < SD.q → ∀ v ∈ SD.U i, v ≠ SD.rep i →
        v ≠ (fun i => if h : i < (Fama.unitBlocks γ S σ Mk).length then ((Fama.unitBlocks γ S σ Mk).get ⟨i, h⟩).lower else v0) i →
        4 ≤ S.molecule.deg v := by
      intro i hi v hv hvr hvl
      rw [spliceDataOf_UMk S hM σ Mk v0 hi] at hv
      rw [spliceDataOf_repMk S hM σ Mk v0 hi] at hvr
      have hvl' : v ≠ ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).lower := by
        have hi' : i < (Fama.unitBlocks γ S σ Mk).length := hi
        intro h; apply hvl; show v = if h : i < (Fama.unitBlocks γ S σ Mk).length then _ else _
        rw [dif_pos hi']; exact h
      have hB := ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).isBlock
      have := hB.2.2.2.2.2.2.2.2.1 v hv hvr hvl'
      exact this ▸ degIn_le_deg S.molecule _ v
    have h1 := deficit_splice_le SD (fun v => Finset.mem_univ v) (fun c => Finset.mem_univ c) hM hM' _ hint
    have h2 := sum_deficit_le (stSt γ S σ Mk).G.molecule hM' (ladderFamOf (stSt γ S σ Mk).G) (ladderFamOf_disj (stSt γ S σ Mk).G hM')
    have h3 := ladderFamOf_r (stSt γ S σ Mk).G
    have h4 : SD.q = (Fama.unitBlocks γ S σ Mk).length := rfl
    omega
  · have hemp : IsEmpty (GBranch S.tree) := not_nonempty_iff.1 hne
    have : ∑ v ∈ S.molecule.atoms, (4 - S.molecule.deg v) = 0 :=
      Finset.sum_eq_zero fun v _ => (hemp.false v).elim
    omega

end inst

end WaveTurbulence.GammaLow.Famc.ClassCount
