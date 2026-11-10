/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.Align.Export` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassBoundary
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.ClassKernels
public import WaveTurbulence.Foundations.Vine.Align.Export
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineIngredientCarrier
/-! S2 geometry and class-set export. The actual common-garden shape, route,
boundary, unit index, hinges and output-set bridge are supplied here.
Native outer-slot kernels also agree as complete functions of times and momentum. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.VineAlign WaveTurbulence.GammaLow.FinalCount
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine WaveTurbulence.GammaLow.FinalCount
open _root_.WaveTurbulence.Represents
open _root_.WaveTurbulence.VineA

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Pull the representative's actual layering to its decoded reconstruction. -/
noncomputable def sourceLayer (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) :
    GNode (a.prime.data.forest a.prime.prime.1) → ℕ :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose

theorem sourceLayer_isLayering {w : ℕ} (a : PrescribedPrimeGarden γ w) :
    IsLayering (a.prime.data.garden a.prime.prime.1) (sourceLayer γ a) :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose_spec.choose

theorem sourceLayer_reconstructs {w : ℕ} (a : PrescribedPrimeGarden γ w) :
    layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer γ a) (sourceLayer_isLayering a) = a.layered :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose_spec.choose_spec

/-- B1a: the actual unit assembly family for the marking `mk` (the units are the runs of the marked groups, so the
start family consists of unmarked vines only); main's `sourceAssembly γ a` is its value at the empty marking. -/
noncomputable abbrev sourceAssemblyMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w) :=
  alignedAssemblyMk γ (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)

/-- B1a: the unit regions for the marking `mk`. -/
noncomputable abbrev sourceUnitsMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w) :=
  Famb.VineC.unitsRegionΓ (sourceAssemblyMk γ a mk) (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))

/-- The actual unit assembly family to use as `B₀` in the S2 class sum. -/
noncomputable abbrev sourceAssembly (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) :=
  sourceAssemblyMk γ a fun _ => ∅

noncomputable abbrev sourceStart (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w := fun _ => ∅) :=
  Famb.VineC.unitsStartΓ (sourceAssemblyMk γ a mk) (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
    a.prime.data a.prime.prime.1 (sourceLayer γ a) (sourceLayer_isLayering a)

noncomputable abbrev sourceUnits (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) :=
  sourceUnitsMk γ a fun _ => ∅

noncomputable abbrev sourceClass (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (a : PrescribedPrimeGarden γ w) (p : ℕ) (kind : Bool)
    (mk : Stage1Mk.MarkFn γ w := fun _ => ∅) :=
  classU (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a mk)) p kind (sourceStart γ a mk) (sourceUnitsMk γ a mk)

section SourceMk
/-! B1b-3: the exported class-shape lemmas at a marking `mk`. A member `y` of `sourceClass γ a p kind mk` carries the
marking `mkY` (`SourceMemberMarked`); the shapes land on the representative's spliced garden at `mk a.prime`. -/
variable {w p : ℕ} {kind : Bool}

/-- B1b-3: the member `y` of the marked source class carries `mkY` along every actual trace. -/
abbrev SourceMemberMarked (γ : ℝ) [Fact (γ ≤ 1 / 2)] (a : PrescribedPrimeGarden γ w) (p : ℕ) (kind : Bool) (mk : Stage1Mk.MarkFn γ w)
    (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a mk))) (mkY : Set (CLVineG γ y.1.skeleton)) : Prop :=
  MemberMarked γ p kind (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) y mkY

/-- B1b-3: the empty marking is carried to every member of the unmarked source class. -/
theorem sourceMemberMarked_empty (a : PrescribedPrimeGarden γ w) (p : ℕ) (kind : Bool)
    (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a fun _ => ∅))) : SourceMemberMarked γ a p kind (fun _ => ∅) y ∅ :=
  memberMarked_empty p kind _ _ _ _ _ _ y

/-- B1b-3 (Mk-general form of `sourceClass_hT`). -/
theorem sourceClass_hTMk (a : PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind) mk) :
    (T : Set (LayeredGarden w)) = (sourceStart γ a mk).allCoreOutputs (p := p) (kind := kind) :=
  classSum_hTMk a mk T hT (sourceLayer γ a) (sourceLayer_isLayering a) (sourceLayer_reconstructs a)

variable (a : PrescribedPrimeGarden γ w) (mk : Stage1Mk.MarkFn γ w)
  (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssemblyMk γ a mk))) (hy : y ∈ sourceClass γ a p kind mk)

include hy

/-- B1b-3 (Mk-general form of `sourceShape`): every member maps into the spliced garden at the marking. -/
noncomputable def sourceShapeMk {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY) :
    SpliceShape (fun j => unitClBlock (y.2 j)) (stSt γ a.prime.skeleton a.totalSigma (mk a.prime)).G :=
  classShapeMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `source_disj`). -/
theorem source_disjMk : Disj (fun j => unitClBlock (y.2 j)) :=
  class_disjMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy

/-- B1b-3 (Mk-general form of `sourceShape_hinges`): R-HINGE at the marking. -/
theorem sourceShape_hingesMk {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hinges (source_disjMk a mk y hy) =
      (stSt γ a.prime.skeleton a.totalSigma (mk a.prime)).hinges :=
  classShape_hingesMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `source_upper_tree_index`). -/
theorem source_upper_tree_indexMk (j : Fin (unitBlocks γ a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    (y.2 j).blk.a.1.1 = (sourceUnitsMk γ a mk j).blk.a.1.1 :=
  class_upper_tree_indexMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy j

/-- B1b-3 (Mk-general form of `sourceShape_hmom`). -/
theorem sourceShape_hmomMk {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hmom (source_disjMk a mk y hy) =
      (stShape γ (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)) :=
  classShape_hmomMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `sourceShape_hclk`). -/
theorem sourceShape_hclkMk {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hclk (source_disjMk a mk y hy) =
      (stShape γ (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)) :=
  classShape_hclkMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `sourceShape_route`). -/
theorem sourceShape_routeMk {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY)
    (hG : (stSt γ a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) :
    (sourceShapeMk a mk y hy hT).route y.1.plain hG =
      (stShape γ (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG :=
  classShape_routeMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT hG

/-- B1b-3 (Mk-general form of `sourceShape_slotFn`): R-SLOT at the marking. -/
theorem sourceShape_slotFnMk {d : ℕ} {mkY : Set (CLVineG γ y.1.skeleton)} (hT : SourceMemberMarked γ a p kind mk y mkY)
    (hG : (stSt γ a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ' δ : ℝ)
    (s : ReplacementSlot (stSt γ a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotFn y.1.data y.1.plain L γ' δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((sourceShapeMk a mk y hy hT).iota y.1.plain hG s) =
    slotFn a.prime.data a.prime.prime.1 L γ' δ (typeProfiles a.layered f)
      (sourceLayer γ a) (sourceLayer_isLayering a)
      ((stShape γ (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) := by
  have h := classShape_slotFnMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy hT hG f L γ' δ s
  rw [sourceLayer_reconstructs] at h
  exact h

end SourceMk

/-- `hT` with the representative's actual data and layering, without an alignment assumption. -/
theorem sourceClass_hT {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind)) :
    (T : Set (LayeredGarden w)) = (sourceStart γ a).allCoreOutputs (p := p) (kind := kind) :=
  sourceClass_hTMk a (fun _ => ∅) T hT

/-- Every genuine unit-class member maps into the literal exported profile γ garden. -/
noncomputable def sourceShape (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind) :
    SpliceShape (fun j => unitClBlock (y.2 j)) a.fullProfile.piece.gap.garden :=
  classShape (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer γ a) (sourceLayer_isLayering a) a.prime.prime y hy

theorem source_disj {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ w)
    (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind) :
    Disj (fun j => unitClBlock (y.2 j)) :=
  source_disjMk a (fun _ => ∅) y hy

/-- R-HINGE with the producer's literal profile γ hinge set. -/
theorem sourceShape_hinges {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind) :
    (sourceShape γ a y hy).hinges (source_disj a y hy) = a.fullProfile.piece.hinges :=
  sourceShape_hingesMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- R-IDX on the exact class member and source-unit carriers. -/
theorem source_upper_tree_index {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ w)
    (y : UState w (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind)
    (j : Fin (unitBlocks γ a.prime.skeleton a.totalSigma).length) :
    (y.2 j).blk.a.1.1 = (sourceUnits γ a j).blk.a.1.1 :=
  source_upper_tree_indexMk a (fun _ => ∅) y hy j

/-- The complete prescribed-point `hmom` field is common across the class. -/
theorem sourceShape_hmom {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind) :
    (sourceShape γ a y hy).hmom (source_disj a y hy) =
      (profileShape γ a).hmom (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  sourceShape_hmomMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- The complete prescribed-point `hclk` field is common across the class. -/
theorem sourceShape_hclk {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind) :
    (sourceShape γ a y hy).hclk (source_disj a y hy) =
      (profileShape γ a).hclk (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  sourceShape_hclkMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- The actual prescribed-point route is common across the class. -/
theorem sourceShape_route {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) :
    (sourceShape γ a y hy).route y.1.plain hG = (profileShape γ a).route a.prime.prime.1 hG :=
  sourceShape_routeMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y) hG

/-- R-SLOT on the literal common profile γ garden, for all native type profiles. -/
theorem sourceShape_slotFn {R p d : ℕ} {kind : Bool} (a : PrescribedPrimeGarden γ (2 * R))
    (y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly γ a))) (hy : y ∈ sourceClass γ a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ' δ : ℝ)
    (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotFn y.1.data y.1.plain L γ' δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((sourceShape γ a y hy).iota y.1.plain hG s) =
    slotFn a.prime.data a.prime.prime.1 L γ' δ (typeProfiles a.layered f)
      (sourceLayer γ a) (sourceLayer_isLayering a) ((profileShape γ a).iota a.prime.prime.1 hG s) :=
  sourceShape_slotFnMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y) hG f L γ' δ s

end WaveTurbulence.GammaLow.Fama
