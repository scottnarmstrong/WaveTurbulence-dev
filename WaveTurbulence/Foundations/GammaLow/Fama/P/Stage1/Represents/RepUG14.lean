/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepUG14` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG8
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG14
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
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN11
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyIndex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPhysicalResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyResonances
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySlotResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceAnchors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainInverseRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainLocalWitnesses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOriginGeometry
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOrigins
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainPhysicalCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartTagAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLCoordinateChartTagDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenFormRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhase
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhaseExponent
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixData
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixIdentities
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorIdentity
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedInverseMatrix
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedPredecessorSystem
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLRegionalPhaseSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Weights
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintPredecessors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainChartIndexing
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPrefixBlocks
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.VineChainSumintForm
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.IncohDict
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafWire
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3DataS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.PieceFamily
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrderS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModClass
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModCore
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NestGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8


/-!
# S2 REPRESENTS, G1 in the shape of `exists_hinge_data_units_leaf_w`

`leafFlag γ σ hM j : Fin 3 → Prop`: coordinate `i ∈ {1, 2}` of unit `j` is flagged when its lower child has a root time as `G_sb`
clock (a leaf).  `g1_units`: the hypothesis `G1` of `exists_hinge_data_units_leaf_w` for the units of `stSt γ S σ`, with the dummy
time `td j i = qOutOf … i`.  Its V5-side inputs (named, owner V5-KIND, R74): `qOut i = lay c` for a branch lower child `c`
(`lay_branch_child` computes `lay c` as the layer of the core), and `qOut 1, qOut 2 ≤ qOut 0`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 VineParamContract WaveTurbulence.RegRedLeaf

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The flagged (leaf lower child) clock coordinates of unit `j`. -/
def leafFlag (γ : ℝ) [Fact (γ ≤ 1 / 2)] {Mk : Set (CLVineG γ S)} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (j : Fin (unitBlocks γ S σ Mk).length) : Fin 3 → Prop :=
  fun i => (i = 1 ∧ ∃ r, nodeClk (stSt γ S σ Mk).G ((stShape γ hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j 2) = Sum.inl r) ∨
    (i = 2 ∧ ∃ r, nodeClk (stSt γ S σ Mk).G ((stShape γ hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j 3) = Sum.inl r)

/-- B1b (Mk-general form of `leafFlag_zero`). -/
theorem leafFlag_zeroMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ _)} (j : Fin (unitBlocks γ (Mk := Mk) S σ).length) :
    ¬ leafFlag γ hM σ j 0 := by
  unfold leafFlag
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem leafFlag_zero (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks γ S σ).length) :
    ¬ leafFlag γ hM σ j 0 := leafFlag_zeroMk (Mk := ∅) hM σ j

/-- B1b (Mk-general form of `leafFlag_one`). -/
theorem leafFlag_oneMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ _)} (j : Fin (unitBlocks γ (Mk := Mk) S σ).length) :
    leafFlag γ hM σ j 1 ↔ ∃ r, nodeClk (stSt γ (Mk := Mk) S σ).G ((stShape γ (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 2) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨rfl, h⟩

theorem leafFlag_one (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks γ S σ).length) :
    leafFlag γ hM σ j 1 ↔ ∃ r, nodeClk (stSt γ S σ).G ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inl r := leafFlag_oneMk (Mk := ∅) hM σ j

/-- B1b (Mk-general form of `leafFlag_two`). -/
theorem leafFlag_twoMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ _)} (j : Fin (unitBlocks γ (Mk := Mk) S σ).length) :
    leafFlag γ hM σ j 2 ↔ ∃ r, nodeClk (stSt γ (Mk := Mk) S σ).G ((stShape γ (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 3) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by decide)
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

theorem leafFlag_two (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks γ S σ).length) :
    leafFlag γ hM σ j 2 ↔ ∃ r, nodeClk (stSt γ S σ).G ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inl r := leafFlag_twoMk (Mk := ∅) hM σ j

open scoped Classical in
/-- B1b (Mk-general form of `g1_units`). -/
theorem g1_unitsMk (P : WTParams) (hM : S.molecule.IsMolecule) (σ : Prescription S) (hM9 : Famb.NormalChartSupply γ)
    {Mk : Set (CLVineG γ _)} {n₀ : Fin (unitBlocks γ (Mk := Mk) S σ).length → ℕ}
    {B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ S (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) (n₀ j)}
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (base : Mom P.d) (tt : Fin w → ℝ)
    (roots : Fin w → (Fin P.d → ℤ)) (selSk : GenDecoration (stSt γ (Mk := Mk) S σ).G P.d roots 0 → Prop)
    (centre : Fin (unitBlocks γ (Mk := Mk) S σ).length → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d)
    (hb1 : ∀ j c, nodeClk (stSt γ (Mk := Mk) S σ).G ((stShape γ (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 2) = Sum.inr c →
      qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 1 =
        (stSt γ (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hb2 : ∀ j c, nodeClk (stSt γ (Mk := Mk) S σ).G ((stShape γ (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 3) = Sum.inr c →
      qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 2 =
        (stSt γ (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hqle : ∀ j, qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 0) :
    ∀ κ : GenDecoration (stSt γ (Mk := Mk) S σ).G P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain (stSt γ (Mk := Mk) S σ).G
        ((stSt γ (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG))) tt, ∀ j (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape γ (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        (fun i => if leafFlag γ hM σ j i then
            ((qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) i : ℕ) : ℝ)
          else clockOf (stSt γ (Mk := Mk) S σ).G tt τ ((stShape γ (Mk := Mk) hM σ).hclk (unitBlkMk_disj (Mk := Mk) hM σ) j i)) ∈
          outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) := by
  intro κ _ τ hτ j c _
  refine g1_weak (stShape γ (Mk := Mk) hM σ) (unitBlkMk_disj (Mk := Mk) hM σ) j tt _ hτ
    (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) ?_ (hb1 j) (hb2 j) (hqle j).1 (hqle j).2
    (leafFlag γ hM σ j) (leafFlag_zeroMk (Mk := Mk) hM σ j) (leafFlag_oneMk (Mk := Mk) hM σ j) (leafFlag_twoMk (Mk := Mk) hM σ j)
  exact (lay_hingeMk (Mk := Mk) hM σ j RD hG layer hLayer).symm

open scoped Classical in
theorem g1_units (P : WTParams) (hM : S.molecule.IsMolecule) (σ : Prescription S) (hM9 : Famb.NormalChartSupply γ)
    {n₀ : Fin (unitBlocks γ S σ).length → ℕ}
    {B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ S (regionOf (unitBlk γ hM σ j)) (n₀ j)}
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (base : Mom P.d) (tt : Fin w → ℝ)
    (roots : Fin w → (Fin P.d → ℤ)) (selSk : GenDecoration (stSt γ S σ).G P.d roots 0 → Prop)
    (centre : Fin (unitBlocks γ S σ).length → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d)
    (hb1 : ∀ j c, nodeClk (stSt γ S σ).G ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inr c →
      qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 1 =
        (stSt γ S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hb2 : ∀ j c, nodeClk (stSt γ S σ).G ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inr c →
      qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 2 =
        (stSt γ S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hqle : ∀ j, qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) 0) :
    ∀ κ : GenDecoration (stSt γ S σ).G P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain (stSt γ S σ).G
        ((stSt γ S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG))) tt, ∀ j (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        (fun i => if leafFlag γ hM σ j i then
            ((qOutOf RD hG layer (unitBlk γ hM σ j).upper (unitBlk γ hM σ j).lower (regionOf (unitBlk γ hM σ j)) i : ℕ) : ℝ)
          else clockOf (stSt γ S σ).G tt τ ((stShape γ hM σ).hclk (unitBlk_disj hM σ) j i)) ∈
          outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) := g1_unitsMk (Mk := ∅) P hM σ hM9 RD hG layer hLayer base tt roots selSk centre hb1 hb2 hqle

/-- B1b (Mk-general form of `qOut_le_qOut_zero`). -/
theorem qOut_le_qOut_zeroMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ _)} (j : Fin (unitBlocks γ (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hb : qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 1 ≤
        layer (RD.coreBranch hG (unitBlkMk γ (Mk := Mk) hM σ j).lower).toNode ∧
      qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 2 ≤
        layer (RD.coreBranch hG (unitBlkMk γ (Mk := Mk) hM σ j).lower).toNode) :
    qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlkMk γ (Mk := Mk) hM σ j).upper (unitBlkMk γ (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk γ (Mk := Mk) hM σ j)) 0 := by
  have hle := layer_core_le_upper (unitBlkMk γ (Mk := Mk) hM σ j) RD hG layer hLayer (unitBlkMk γ (Mk := Mk) hM σ j).lower
    (unitBlkMk γ (Mk := Mk) hM σ j).isBlock.2.2.1
  exact ⟨hb.1.trans hle, hb.2.trans hle⟩


end WaveTurbulence.GammaLow.Fama.Represents
