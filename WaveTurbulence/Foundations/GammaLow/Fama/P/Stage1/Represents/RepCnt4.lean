/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepCnt4` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.J.Incoh
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCnt2
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt4
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8
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


/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 4: the clauses `1 ≤ r̄ ≤ N` and `ḡ ≤ N` of the successor piece

For `VineA.NormalizedSplice.stage1PieceOf` of a skeleton `S` with `1 ≤ n_sk`, `n_sk ≤ N` (and `n_sk + |D| ≤ N` for `ḡ`):
* `n_sb + #hinges ≤ n_sk` (each unit has at least two atoms, one crown per unit);
* `r̄ = ρ_sb + #hinges ≤ n_sb + #hinges ≤ N`, `1 ≤ r̄`;
* `ḡ = g_reg + Σ vineIncoh + g_sb ≤ |D|/2 + (n_sb + Σ_u (|u| - 1)) ≤ N`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount

variable {R : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



/-- B1b (Mk-general form of `stage1Piece_rbar_bounds`). -/
theorem stage1Piece_rbar_boundsMk (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hn : 1 ≤ S.order) (hN : S.order ≤ N) {Mk : Set (CLVineG γ _)} :
    1 ≤ (VineA.NormalizedSplice.stage1PieceOf γ (Mk := Mk) d hS LG hd σ).rbar ∧
      (VineA.NormalizedSplice.stage1PieceOf γ (Mk := Mk) d hS LG hd σ).rbar ≤ N := by
  have hM : S.molecule.IsMolecule := Mole.garden_isMolecule S
  have hMsb : (stSt γ (Mk := Mk) S σ).G.molecule.IsMolecule := Mole.garden_isMolecule _
  have hpos : 1 ≤ (stSt γ (Mk := Mk) S σ).G.order := (stSt γ (Mk := Mk) S σ).M.order_pos (stSt γ (Mk := Mk) S σ).hcls hn
  have hat : (stSt γ (Mk := Mk) S σ).G.molecule.atoms.card = (stSt γ (Mk := Mk) S σ).G.order := garden_card_atoms _
  have h1 := rho_le_atoms hMsb
  have h2 := one_le_rho (M := (stSt γ (Mk := Mk) S σ).G.molecule) (by omega)
  have h3 := order_add_hinges_leMk (Mk := Mk) hM σ
  show 1 ≤ (stSt γ (Mk := Mk) S σ).G.molecule.rho + (stSt γ (Mk := Mk) S σ).hinges.card ∧ (stSt γ (Mk := Mk) S σ).G.molecule.rho + (stSt γ (Mk := Mk) S σ).hinges.card ≤ N
  omega

theorem stage1Piece_rbar_bounds (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hn : 1 ≤ S.order) (hN : S.order ≤ N) :
    1 ≤ (VineA.NormalizedSplice.stage1PieceOf γ d hS LG hd σ).rbar ∧
      (VineA.NormalizedSplice.stage1PieceOf γ d hS LG hd σ).rbar ≤ N := stage1Piece_rbar_boundsMk (Mk := ∅) d hS LG hd σ hn hN

/-- B1b (Mk-general form of `stage1Piece_gbar_le`). -/
theorem stage1Piece_gbar_leMk (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hN : S.order + D.size ≤ N) {Mk : Set (CLVineG γ _)} :
    (VineA.NormalizedSplice.stage1PieceOf γ (Mk := Mk) d hS LG hd σ).gbar ≤ N := by
  have hM : S.molecule.IsMolecule := Mole.garden_isMolecule S
  have hMsb : (stSt γ (Mk := Mk) S σ).G.molecule.IsMolecule := Mole.garden_isMolecule _
  have hat : (stSt γ (Mk := Mk) S σ).G.molecule.atoms.card = (stSt γ (Mk := Mk) S σ).G.order := garden_card_atoms _
  have h1 := sum_vineIncoh_le_unitsMk (Mk := Mk) hM σ (RegRed.coreLayer LG D hS hd)
  have h2 := totalIncoherency_le_atoms hMsb (ladderDataOf (stSt γ (Mk := Mk) S σ).G)
    ((stSt γ (Mk := Mk) S σ).layer (RegRed.coreLayer LG D hS hd))
  have h3 := order_add_units_leMk (Mk := Mk) hM σ
  have h4 : 2 * gregOf D hS LG ≤ D.size := WaveTurbulence.Represents.two_mul_gregOf_le D hS LG
  show gskOf γ (Mk := Mk) (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) +
    (ladderDataOf (stSt γ (Mk := Mk) S σ).G).totalIncoherency ((stSt γ (Mk := Mk) S σ).layer (RegRed.coreLayer LG D hS hd)) ≤ N
  unfold gskOf
  omega

theorem stage1Piece_gbar_le (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hN : S.order + D.size ≤ N) :
    (VineA.NormalizedSplice.stage1PieceOf γ d hS LG hd σ).gbar ≤ N := stage1Piece_gbar_leMk (Mk := ∅) d hS LG hd σ hN

end WaveTurbulence.GammaLow.Fama.Represents
