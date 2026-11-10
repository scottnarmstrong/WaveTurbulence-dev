/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedGapIndicator` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineGroupCandidateMapSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizationNamesSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.RepPr2Supp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineCoarseGroupCodeSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineBatchSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineFamilySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineOperationSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRebaseSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRecoverySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRefinementSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizedRepSelSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescriptionSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrimeStateSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineUnitCoverSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedGroupGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepGap
public import WaveTurbulence.Foundations.Vine.A.VineMolDecoration
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseWordBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSpliceDecorationLift
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGapIndicator
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineBatchSplice
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseCodeWord
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCollectionGeometry
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCollectionTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineContributingGroups
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDartAddress
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDesignatedSupport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapJointChoice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupCandidateMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupKeyDiagrams
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCovariance
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVCObjectGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHyperDesignation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHyperGapChoice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedDesigCovariance
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedDesigData
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedDesignatedSupport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedHVCGroupGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedOrdinaryGroupGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepAudit
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineObjectExt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineObjectGeometry
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineOperationSplice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitDeletedDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceBranch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceChildren
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOrdered
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOuter
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
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
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.PieceFamily
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrderS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NestGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8
/-! Complete actual successor gap indicators on the spliced decoration carrier. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine Mole WaveTurbulence.GammaLow.FinalCount
variable {w d : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



/-- The actual successor gap product, with its independently constructed entries. -/
noncomputable def gapValue (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (L γ' η : ℝ) (base : Mom d)
    (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ)) : ℝ :=
  gapProduct (stSt γ G σ).G (gapSpecification γ G σ) L γ' η base z

/-- B1b-3 (Mk-general form of `gapValue`): the gap product with the entries `gapSpecificationMk γ G σ Mk`. -/
noncomputable def gapValueMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) (L γ' η : ℝ) (base : Mom d)
    (z : GNode (stSt γ G σ Mk).G.tree → (Fin d → ℤ)) : ℝ :=
  gapProduct (stSt γ G σ Mk).G (gapSpecificationMk γ G σ Mk) L γ' η base z

/-- B1b-3 (Mk-general form of `gapValue_eq_indicator`). -/
theorem gapValue_eq_indicatorMk (σ : Prescription G) {Mk : Set (CLVineG γ G)} (D : SplicedKernelData (stSt γ G σ Mk).G d)
    (hD : D.gapSpecification = gapSpecificationMk γ G σ Mk) (L γ' η : ℝ) (base : Mom d)
    (z : GNode (stSt γ G σ Mk).G.tree → (Fin d → ℤ)) :
    gapValueMk γ G σ Mk L γ' η base z = splicedGapIndicator (stSt γ G σ Mk).G D L γ' η base z := by
  rw [indicator_eq_gapProduct, hD]
  rfl

open scoped Classical in
/-- B1b-3: **the exact statement of B2c's `VineA.NormalizedSplice.splicedGapIndicator_eq_selOfMk`** (branch
w/mk-subpro, ruling R171), at one garden, prescription and marking. A HYPOTHESIS here, discharged at the joint
landing by `fun … => splicedGapIndicator_eq_selOfMk (Mole.garden_isMolecule G) σ …`. -/
def SplicedGapIndicatorSelOfAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) : Prop :=
  ∀ {d : ℕ} (L γ' η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (_hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (_hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt γ G σ Mk).G.tree → (Fin d → ℤ))
    (_hlab : ∀ y, bondIndex (stSt γ G σ Mk).G zsb y = bondIndex G z ((stSt γ G σ Mk).M.od y))
    (D : SplicedKernelData (stSt γ G σ Mk).G d) (_hD : D.gapSpecification = gapSpecificationMk γ G σ Mk),
    splicedGapIndicator (stSt γ G σ Mk).G D L γ' η base zsb =
      if selOf γ (GroupPrescription.ofPrescription γ σ) L γ' η base z then 1 else 0



/-- B1b-3: at the empty marking the hypothesis is main's `splicedGapIndicator_eq_selOf`. -/
theorem splicedGapIndicatorSelOfAt_empty (G : Garden w) (σ : Prescription G) : SplicedGapIndicatorSelOfAt γ G σ ∅ :=
  fun L γ' η base c z hκ hc0 zsb hlab D hD =>
    splicedGapIndicator_eq_selOf (Mole.garden_isMolecule G) σ L γ' η base c z hκ hc0 zsb hlab D hD

open scoped Classical in
/-- B1b-3: the dart-label form of the same identity (the Mk-general form of main's `gapValue_eq_selDarts`), at one
garden, prescription and marking. B2c's per-group lemma `gapSpecificationMk_indicator_iff` is already dart-label,
and B2c's proof of `splicedGapIndicator_eq_selOfMk` proves this verbatim with `bondIndex G z` replaced by `κ`. It is
needed for twist invariance (`unitSplice_actual_gapValueMk`), where the source labels are the pull-back
`κ ∘ Z.iso.d` of a target decoration (no node decoration of the source is available). A HYPOTHESIS here. -/
def GapValueSelDartsAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) : Prop :=
  ∀ {d : ℕ} (L γ' η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (_hκ : G.molecule.IsDecoration L base c κ)
    (_hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt γ G σ Mk).G.tree → (Fin d → ℤ))
    (_hlab : ∀ y, bondIndex (stSt γ G σ Mk).G zsb y = κ ((stSt γ G σ Mk).M.od y)),
    gapValueMk γ G σ Mk L γ' η base zsb = if selDarts γ (GroupPrescription.ofPrescription γ σ) L γ' η base κ then 1 else 0


/-- The literal kernel's gap indicator is this product when it carries the constructed entries. -/
theorem gapValue_eq_indicator (σ : Prescription G) (D : SplicedKernelData (stSt γ G σ).G d)
    (hD : D.gapSpecification = gapSpecification γ G σ) (L γ' η : ℝ) (base : Mom d)
    (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ)) :
    gapValue γ G σ L γ' η base z = splicedGapIndicator (stSt γ G σ).G D L γ' η base z := by
  rw [indicator_eq_gapProduct, hD]
  rfl

open scoped Classical in
/-- The exact gap product is the restriction on original conserving dart labels. -/
theorem gapValue_eq_selDarts (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (L γ' η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (κ))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt γ G σ).G zsb y = κ ((stSt γ G σ).M.od y))
    :
    gapValue γ G σ L γ' η base zsb =
      if selDarts γ (GroupPrescription.ofPrescription γ σ) L γ' η base κ then 1 else 0 := by
  classical
  set Q : GBranch (stSt γ G σ).G.tree → Prop := fun v => ∀ q, gapSpecification γ G σ v = some q →
        Molecule.gapKind L γ' η ((base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.second))) = q.kind with hQ
  have hf : gapValue γ G σ L γ' η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold gapValue gapProduct
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (stSt γ G σ).G.tree))) (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ' η ((base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt γ G σ).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ selDarts γ (GroupPrescription.ofPrescription γ σ) L γ' η base κ := by
    constructor
    · intro hall
      unfold selDarts
      intro S
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ S.2 L γ' η base c _ hκ hc0
        (bondIndex (stSt γ G σ).G zsb) hlab
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ' η base (κ) hO
      have := (hind k hk).mp (hall _ e he)
      exact hgk.trans this
    · intro hsel v q hq
      have hsome : (gapSpecification γ G σ v).isSome := by rw [hq]; rfl
      obtain ⟨S, hS, hSv⟩ := (gapSpecification_isSome_iff hM σ v).mp hsome
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ hS L γ' η base c _ hκ hc0
        (bondIndex (stSt γ G σ).G zsb) hlab
      have hat : groupAtom γ G σ S = some ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) := by
        unfold groupAtom; rw [ha]; rfl
      rw [hat] at hSv
      cases hSv
      rw [he] at hq
      cases hq
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ' η base (κ) hO
      exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

/-- B1b-3: at the empty marking the dart-label hypothesis is main's `gapValue_eq_selDarts`. -/
theorem gapValueSelDartsAt_empty (G : Garden w) (σ : Prescription G) : GapValueSelDartsAt γ G σ ∅ :=
  fun L γ' η base c κ hκ hc0 zsb hlab =>
    gapValue_eq_selDarts (Mole.garden_isMolecule G) σ L γ' η base c κ hκ hc0 zsb hlab

/-- B1b-3 (Mk-general form of `unitSplice_actual_gapValue`): twist invariance of the gap product at markings carried
by the twist, given the dart-label gap identity at the source and target (`GapValueSelDartsAt`, B2c). -/
theorem unitSplice_actual_gapValueMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (hgS : GapValueSelDartsAt γ G σ Mk) (hgT : GapValueSelDartsAt γ Z.target (transportPrescription Z.iso σ) Mk')
    {L : ℝ} (hL : L ≠ 0) (γ' η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G d roots 0) :
    gapValueMk γ G σ Mk L γ' η base (z.1 ∘ unitSpliceNodeEquivMk γ Z σ hT hsel) =
      gapValueMk γ Z.target (transportPrescription Z.iso σ) Mk' L γ' η base z.1 := by
  classical
  obtain ⟨κ, hlab⟩ := splice_labels_extendMk hH (transportPrescription Z.iso σ) hL base roots z
  let c := gardenSource Z.target hH (fun i => base + latticePoint L (roots i))
  have hκ := spliced_molecule_decoration Z.target hH hL base roots κ
  have hc0 : ∀ v ∈ Z.target.molecule.atoms, Z.target.molecule.deg v = 4 → c v = 0 :=
    fun v _ hv => gardenSource_eq_zero_of_deg_four Z.target hH _ v hv
  have hpull := molIso_decoration_pull Z.iso L base c (bondIndex Z.target κ.1) hκ
  have hzero : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → (c ∘ Z.iso.e) v = 0 := by
    intro v hv hd
    exact hc0 (Z.iso.e v) ((Z.iso.atoms_iff v).mpr hv) ((Z.iso.deg_img v).trans hd)
  have hsLab : ∀ y, bondIndex (stSt γ G σ Mk).G (z.1 ∘ unitSpliceNodeEquivMk γ Z σ hT hsel) y =
      (bondIndex Z.target κ.1 ∘ Z.iso.d) ((stSt γ G σ Mk).M.od y) := by
    intro y
    exact (unitSplice_bondIndexMk Z σ hT hsel z.1 y).trans
      ((hlab _).trans (congrArg (bondIndex Z.target κ.1) (unitSpliceMolIso_dart_namesMk Z σ hT hsel y)))
  rw [hgS L γ' η base _ _ hpull hzero _ hsLab, hgT L γ' η base c _ hκ hc0 _ hlab]
  obtain ⟨u, hu, ha⟩ := hsel
  have hc := selDarts_twist Z ⟨u, mem_allSG hu.1, ha⟩ (Represents.GroupPrescription.ofPrescription γ σ)
    L γ' η base c (bondIndex Z.target κ.1) hκ hc0
  exact if_congr hc.symm rfl rfl


end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
