/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVD8` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD7
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD8
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU7
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG14
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVC3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD6
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFullA4
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Export
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
# S2 REPRESENTS, session 12: the member identity `hV` of the class sum (B3)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic MeasureTheory

variable {p : ℕ} {kind : Bool} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

open scoped Classical in
theorem member_hV {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA γ R p kind A)
    (a : VineA.PrescribedPrimeGarden γ (2 * R)) (hπ : repPt γ π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a)),
      y ∈ sourceClass γ a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer γ a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape γ a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn a.prime.data a.prime.prime.1 P.L P.γ P.δ
        (typeProfiles a.layered (U.h i)) (sourceLayer γ a) (sourceLayer_isLayering a)
        ((profileShape γ a).iota a.prime.prime.1 hG s') ts x))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind)
    (hctrl : U.toLF.Controlled y.1.layered) :
    (U.toLF.valueSel tt base roots y.1.layered (selP γ p kind A P base roots π y.1.layered) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC γ a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape γ a).route a.prime.prime.1 hG)
            ((profileShape γ a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape γ a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlk γ (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    ∧ ∀ i : U.ι, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC γ a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape γ a).route a.prime.prime.1 hG)
            ((profileShape γ a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape γ a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlk γ (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) := by
  obtain ⟨M, hr, hn, hsh⟩ := sourceShape_data a y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hrel : VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) (repPt γ π) (memberPoint γ a y M hr) :=
    hπ ▸ memberPoint_related' a y hy M hr
  have hsel : selP γ p kind A P base roots π y.1.layered = fun κ => selAt γ P base
      ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩
      (VineA.transportGroupPrescription γ (batchMolIso hr.batch) a.sigma) κ :=
    funext fun κ => propext (selP_iff_related P base roots π (memberPoint γ a y M hr) hrel y.1.layered rfl κ)
  rw [hsel, valueSel_selAt_reconstruction U.toLF y.1.data (VineA.batch_prime hr.batch a.prime.prime)
    (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered (stateLayer_spec y.1) y.1.decodes
    (VineA.transportGroupPrescription γ (batchMolIso hr.batch) a.sigma) tt base roots]
  have hZ : ∀ κ : GenDecoration y.1.skeleton P.d roots 0,
      (if VineA.NormalizedSplice.selOf γ (VineA.transportGroupPrescription γ (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1
        then (1 : ℝ) else 0) =
      (fun z => if selSkC γ a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0)
        ((sourceShape γ a y hy).resDec y.1.plain (source_disj a y hy) κ) := by
    intro κ
    rw [hsh]
    exact (hZ_common a hr hn hL0 P.γ P.η base roots κ).trans
      (selSkC_ite a P.L P.γ P.η hL0 base roots _)
  have hctrl' : U.toLF.Controlled (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) := by
    rw [stateLayer_spec y.1]; exact hctrl
  have hF : ∀ i j, HF y.1.data y.1.plain P.L (unitProfile (fun j => unitClBlock (y.2 j)) (U.h i) j)
      (stateLayer y.1) base := fun i j =>
    hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p (NNReal.coe_nonneg (U.b i))
      (hlay y hy) (fun q j j' hq => hB i q j j' hq) j
  have hexp : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer γ a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape γ a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn y.1.data y.1.plain P.L P.γ P.δ
        (typeProfiles (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
          (U.h i)) (stateLayer y.1) (stateLayer_isLayering y.1) ((sourceShape γ a y hy).iota y.1.plain hG s') ts x) := by
    intro i s' ts hts x
    rw [stateLayer_spec y.1, sourceShape_slotFn a y hy hG (U.h i) P.L P.γ P.δ s']
    exact hexpR i s' ts hts x
  have key := member_modes U (sourceShape γ a y hy) (source_disj a y hy) y.1.data y.1.plain hG (stateLayer y.1)
    (stateLayer_isLayering y.1) hctrl' hd1 hL1 tt base roots
    (fun κ => VineA.NormalizedSplice.selOf γ (VineA.transportGroupPrescription γ (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1)
    (fun z => if selSkC γ a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hZ hF fam
    (fun i s' => slotBox p (fun b => sourceLayer γ a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape γ a).iota a.prime.prime.1 hG s')) hexp
    (fun i τ hτ s' => sourceShape_hbox a y hy hG tt htt τ hτ s')
  refine ⟨?_, fun i => ?_⟩
  · rw [key.1, member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy]
    simp only [member_ker_eq a y hy]
  · have h := key.2 i
    rw [member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy] at h
    simp only [member_ker_eq a y hy] at h
    exact h

end WaveTurbulence.GammaLow.Fama.Represents
