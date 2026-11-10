/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: every unit of `Fama.unitBlocks γ G σ` is a unit code (UL)

`unit_decode`: for a unit `u ∈ Fama.unitBlocks γ G σ` there are ingredient codes `cs` and a labelling `lab` of the atoms of `u`
by `0 … unitWeight cs`, injective on `u.atoms`, whose arcs (the oriented bonds of `G` inside `u.atoms`) are `unitArcs cs`.
Cases: a whole-group unit (`whole_vc`: the group is a VC), or a skip-run `L₀`/`R₀` of an SG group around a skipped
ingredient (`Fama.SkipData`; the runs are chains by `Fama.ingredient_runs`, identified with `L₀`, `R₀` by `left_run_eq`,
`right_run_eq`); for an HVC the Fama.chain lives in `eraseBond G.molecule e`, and `groupArcs_erase` transfers the arcs.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]


theorem skel_a_not_R0 {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule V D'} {S A L0 R0 : Finset V}
    {a b x y : V} (sk : SkelDecomp N S A L0 R0 a b x y) : a ∉ R0 := by
  intro ha
  have hxy : x ≠ y := sk.hA.2.2.2.1
  rcases sk.hL with ⟨-, hxa⟩ | ⟨-, hLB, hLI⟩
  · have : a ∈ R0 ∩ A := by
      refine Finset.mem_inter.mpr ⟨ha, ?_⟩
      rw [← hxa]; exact sk.hA.2.1
    rcases sk.hR with ⟨h0, -⟩ | ⟨-, -, hRI⟩
    · rw [h0] at ha; simp at ha
    · rw [hRI, Finset.mem_singleton] at this
      exact hxy (hxa.trans this)
  · exact Finset.disjoint_right.mp sk.hd ha hLB.2.1


end WaveTurbulence.GammaLow.Famc.ClassCount
