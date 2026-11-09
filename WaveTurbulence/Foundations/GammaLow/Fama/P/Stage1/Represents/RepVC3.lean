/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVC3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Export
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC0
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC3
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
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG14
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN11
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseCodeWord
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseWordBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineObjectExt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSpliceDecorationLift
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Assembly
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.BatchKernels
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Boundary
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.BoundaryOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassBoundary
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassKernels
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassRoute
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassShape
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.CoreAssembly
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Excluded
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.FirstPort
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Hinge
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.MemberKernels
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.MemberShape
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.MemberUnits
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.NodeTrace
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.OperationKernels
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.OperationSlots
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Outputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Shape
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.SurvivingSlots
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.Vine.C.VCSigma
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG15
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVB12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineIngredientCarrier


/-!
# S2 REPRESENTS, session 11: the prescribed point of a unit-class member

For `y` in the unit class `sourceClass γ a p kind`, the prescribed prime garden `memberPoint γ a y` (actual layered garden, prime data
and the actual sigma transport along the unit batch) has the code γ of `a`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign

variable {w p : ℕ} {kind : Bool} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `member_trace`): a member of the run class at the marking `mk` is reached by a full
batch of the run assembly. -/
theorem member_traceMk (a : VineA.PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w)
    (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a mk))) (hy : y ∈ sourceClass γ a p kind mk) :
    ∃ M : List (Famb.VineC.UnitsIndexΓ (sourceAssemblyMk γ a mk)), M.Perm Finset.univ.toList ∧
      ReachU p kind (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a mk)).Q M (sourceStart γ a mk) (sourceUnitsMk γ a mk) y.1 y.2 :=
  (mem_classU a.prime.prime).mp hy

theorem member_trace (a : VineA.PrescribedPrimeGarden γ w) (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)))
    (hy : y ∈ sourceClass γ a p kind) :
    ∃ M : List (Famb.VineC.UnitsIndexΓ (sourceAssembly γ a)), M.Perm Finset.univ.toList ∧
      ReachU p kind (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)).Q M (sourceStart γ a) (sourceUnits γ a) y.1 y.2 :=
  (mem_classU a.prime.prime).mp hy

/-- The prescribed point carried by a class member along its (chosen) full batch. -/
noncomputable def memberPoint (γ : ℝ) [Fact (γ ≤ 1 / 2)] (a : VineA.PrescribedPrimeGarden γ w) (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)))
    (M : List (Famb.VineC.UnitsIndexΓ (sourceAssembly γ a)))
    (hr : ReachU p kind (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)).Q M (sourceStart γ a) (sourceUnits γ a) y.1 y.2) :
    VineA.PrescribedPrimeGarden γ w :=
  ⟨y.1.layered, ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩,
    VineA.transportGroupPrescription γ (batchMolIso hr.batch) a.sigma⟩

theorem memberPoint_code (a : VineA.PrescribedPrimeGarden γ w) (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)))
    (M : List (Famb.VineC.UnitsIndexΓ (sourceAssembly γ a)))
    (hr : ReachU p kind (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)).Q M (sourceStart γ a) (sourceUnits γ a) y.1 y.2) :
    (memberPoint γ a y M hr).code = a.code := by
  have hword := VineA.BatchIso.fine_coarseAtomWord (batchMolIso_spec hr.batch) a.totalSigma
    (unitsFamily_isV0Fam (Mole.garden_isMolecule _) a.totalSigma)
  exact VineA.codedPrescription_map (batchMolIso hr.batch) hword a.sigma



open VineA.PrescribedPrimeGarden in
/-- Selection of a piece at a garden `LG` is the selection of any related prescribed point over `LG`. -/
theorem selP_iff_related {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (π : PcA γ R p kind A) (b : VineA.PrescribedPrimeGarden γ (2 * R))
    (hb : VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) (repPt γ π) b) (LG : LayeredGarden (2 * R)) (hLG : b.layered = LG)
    (κ : GenDecoration LG.garden P.d roots 0) :
    selP γ p kind A P base roots π LG κ ↔ selAt γ P base b.prime b.sigma (hLG ▸ κ) := by
  constructor
  · rintro ⟨b', h', hrel', hs'⟩
    have hcode : b'.code = b.code := (VineA.PrescribedPrimeGarden.Related.code_eq hrel').symm.trans (VineA.PrescribedPrimeGarden.Related.code_eq hb)
    have : b' = b := VineA.PrescribedPrimeGarden.eq_of_layered_code (h'.trans hLG.symm) hcode
    subst this
    subst hLG
    exact hs'
  · intro hs
    exact ⟨b, hLG, hb, hs⟩

end WaveTurbulence.GammaLow.Fama.Represents
