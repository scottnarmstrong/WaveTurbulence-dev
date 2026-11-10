/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVD15` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstGamma
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD14
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN10
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE3
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD15
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceAmend7R83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceFinalR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleDesigR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleHingeR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepKC1
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr7
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr9
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepS10b
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG14
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVC1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVC3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD10
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD13
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD7
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD9
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN11
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN7
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineProducer
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCnt2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCnt4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCountA
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepS10a
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG15
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVB12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineIngredientCarrier


/-!
# S2 REPRESENTS, session 12: the vine case at the representative (B4)

`CvineF`: the explicit large constant of the vine case (depends only on `d`, `η` and the gate constant).
`vineCaseRepresents_of_gate`: `VineCaseRepresents {Pg with C₁ := C}` from the two leafwise gates (through `GateEnv Pg`),
V5's `VineEstCanonLayerHalfMK` at the parameter record, and `Famb.NormalChartSupply γ` (M9).
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
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
open scoped ENNReal Classical WaveTurbulence.GammaLow.FinalCount

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The explicit minimal constant of the vine case. -/
noncomputable def CvineF (d : ℕ) (η c₁ : ℝ) : ℝ :=
  max (max (max 1 (2 * c₁ ^ 2 * (1 + cLeib d (30 * d)))) (Cchi d * (nodeBallCard d : ℝ) * Kslot d η ^ 2))
    (Cchi d * (nodeBallCard d : ℝ) * (9 * KslotM d η) ^ 2 * max 1 (ChinF d η))



/-- B1b (Mk-general form of `gsk_of_spec`). -/
theorem gsk_of_specMk {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {Mk : Set (CLVineG γ _)} :
    gskOf γ (Mk := Mk) (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) =
      gskOf γ (Mk := Mk) (gregOf D hS (layeredReconstruction D hS layer hLayer)) S σ (fun v => layer (D.coreBranch hS v).toNode) := by
  subst hspec
  rfl

theorem gsk_of_spec {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    gskOf γ (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) =
      gskOf γ (gregOf D hS (layeredReconstruction D hS layer hLayer)) S σ (fun v => layer (D.coreBranch hS v).toNode) := gsk_of_specMk (Mk := ∅) D hS layer hLayer LG hspec hd σ

theorem nor_card_eq {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : Famb.NormalChartSupply γ) (B : Famb.VineEstS2.CLChainAssemblyΓ γ G R n) :
    (Finset.univ.filter fun i : Fin n => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card =
      (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card := by
  simp only [Famb.VineEstS2.assemblyShapeΓ, shapeFamily]
  congr 1
  ext i
  simp
  exact fun _ => Finset.mem_univ _

theorem normalizedPiece_bsk {R : ℕ} (a : VineA.PrescribedPrimeGarden γ (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).bsk = bskOf γ a.prime.skeleton a.totalSigma := rfl


section VineCase
variable (Pg : WTParams) (C : ℝ) [Fact (Pg.γ ≤ 1 / 2)]

theorem vineCaseRepresents_of_gate (E : GateEnv Pg) (hη : 0 < Pg.η) (hδ : 0 < Pg.δ)
    (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : Famb.NormalChartSupply Pg.γ) (hC : CvineF Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : Famb.VineEstGammaHalfMK (PB Pg C)) :
    VineCaseRepresentsG (PB Pg C) := by
  intro p hp R hR hRmax N hN1 hNmax A hA hcl tt htt base roots U s hs0 hb hsize π hv
  obtain ⟨K, hK1, hKe, hslot⟩ := vine_slot_data (γ := Pg.γ) Pg E
  have hcLeib := cLeib_nonneg Pg.d (30 * Pg.d)
  have hC1' : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hC)
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * K) ^ 2 * max 1 (ChinF Pg.d Pg.η) ≤ C := by
    rw [hKe]; exact le_trans (le_max_right _ _) hC
  have hC1ge : 1 ≤ C := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hC
  obtain ⟨hη6, hη1, hη12⟩ := eta_small_facts Pg.η hη E.hη
  have hCg : Pg.C₁ ≤ C := by nlinarith [E.hC1]
  have hgate : CoherentGateH (PB Pg C) :=
    coherentGateH_of (leafwiseCoherentApproximation30_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hcoh)
  have hinc : IncoherentGateH (PB Pg C) :=
    incoherentGateH_of (leafwiseIncoherentDecay_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hinc)
  have hd1 : 1 ≤ Pg.d := E.hd1
  have hL1 : 1 ≤ Pg.L := E.hL1
  have hL0 : Pg.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  obtain ⟨a, ha⟩ : ∃ a, repPt Pg.γ π = a := ⟨_, rfl⟩
  have haA : a.layered ∈ A := ha ▸ repPt_layered_mem π
  have hcA := hA a.layered haA
  have hcan : IsCanonGC (p + 1) a.layered := hcA.1
  have hdec := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hNmax' : N ≤ Pg.N (p + 1) ^ 4 := by rw [N_bumpC1] at hNmax; exact hNmax
  have hordN : a.layered.garden.order = N := hcA.2.2.1
  have hsz : a.prime.data.size ≤ Pg.N (p + 1) ^ 4 := by omega
  have hGplain : a.fullProfile.piece.gap.garden.IsPlain :=
    (stSt Pg.γ a.prime.skeleton a.totalSigma).plain a.prime.prime.1
  have hctrlA : ∀ LG ∈ A, U.toLF.Controlled LG := controlled_of_bounded hA U hb
  have hctrl_a : ∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i) :=
    fun i => hctrlA _ haA i
  obtain ⟨fam, μ, hexpR, hμ, hμb⟩ := hslot C hC1' a hp hcan hsz tt htt U hctrl_a hGplain
  obtain ⟨T, hT⟩ := exists_outputs_finset (p := p) a
  have hlay := fun y hy x => member_stateLayer_le hA hcl a haA y hy x
  have hctrlM : ∀ y : UState (2 * R) (Famb.VineC.unitsSplitΓ (sourceAssembly Pg.γ a)),
      y ∈ sourceClass Pg.γ a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered :=
    fun y hy => hctrlA _ (outputs_mem_A hcl a haA hcan y hy)
  have hsum := class_sum_modes π a ha (PB Pg C) U hd1 hL1 tt htt base roots hlay hb hctrlM
    hGplain fam hexpR T hT
  have hcanR : IsCanonGC (p + 1) (repPt Pg.γ π).layered := by rw [ha]; exact hcan
  have hTR : (T : Set (LayeredGarden (2 * R))) = (repPt Pg.γ π).outputs (p := p) (kind := objKind (2 * R)) := by
    rw [ha]; exact hT
  rw [sum_members_eq hcl π hcanR _ U.toLF tt base roots T hTR, hsum]
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  letI : Fintype U.ι := U.fin
  have hsgn : ∀ i : U.ι, ‖((U.sign i : ℝ) : ℂ)‖ ≤ 1 := fun i => by
    rw [Complex.norm_real]; exact U.sign_abs_le i
  have key : Stage1PieceG.RepresentsInt (P := (PB Pg C)) (a.normalizedPiece (PB Pg C).d) N tt base roots s
      (∑ i : U.ι, ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden (PB Pg C).L (PB Pg C).γ (PB Pg C).δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC Pg.γ a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z
              then 1 else 0) hGplain
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape Pg.γ a).route a.prime.prime.1 hGplain)
            ((profileShape Pg.γ a).hclk (unitBlk_disj hMa a.totalSigma))
            ((profileShape Pg.γ a).hmom (unitBlk_disj hMa a.totalSigma))
            (fun j lam t k => unitHk (PB Pg C) p (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a)
              (sourceLayer_isLayering a)
              (unitProfile (unitBlk Pg.γ hMa a.totalSigma) (U.h i) j) base lam t k)) := by
    refine representsIntA_of_vineModes (P := (PB Pg C)) hd1 hL1 E.hη0 (a.normalizedPiece (PB Pg C).d) hGplain tt base roots
      (selSkC Pg.γ a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots) ?_
      ((profileShape Pg.γ a).route a.prime.prime.1 hGplain)
      (fun s i => (profileShape Pg.γ a).route_natural a.prime.prime.1 hGplain s i)
      ((profileShape Pg.γ a).hclk (unitBlk_disj hMa a.totalSigma)) ((profileShape Pg.γ a).hmom (unitBlk_disj hMa a.totalSigma))
      (stSrc Pg.γ hMa a.totalSigma hGplain) (fun j i x hx z => stSrc_dart hMa a.totalSigma hGplain j i x hx roots z)
      (fun j i r hr z => stSrc_root hMa a.totalSigma hGplain j i r hr roots z)
      (fun i : U.ι => ((U.sign i : ℝ) : ℂ)) hsgn fam μ
      (fun i j lam t k => unitHk (PB Pg C) p (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a)
        (sourceLayer_isLayering a) (unitProfile (unitBlk Pg.γ hMa a.totalSigma) (U.h i) j) base lam t k)
      (c := 6 * (PB Pg C).η ^ 6) (θ := (PB Pg C).η) (by positivity) hη1 hη12 hμ
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) K (max 1 (ChinF Pg.d Pg.η)) rfl hK1 (le_max_left _ _) hCχ
      (fun s' => slotSize a.prime.data ((profileShape Pg.γ a).iota a.prime.prime.1 hGplain s'))
      (fun s' => slotIncoh a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (sourceLayer_isLayering a)
        ((profileShape Pg.γ a).iota a.prime.prime.1 hGplain s'))
      (fun i s' => slotLeaf a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (sourceLayer_isLayering a) (fun _ => U.b i)
        ((profileShape Pg.γ a).iota a.prime.prime.1 hGplain s'))
      ?_ hμb
      (fun i j => unitMass (PB Pg C) hM9 (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a)
        (sourceLayer_isLayering a) (U.b i))
      (fun j => clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk Pg.γ hMa a.totalSigma j)))
      (fun j => Famb.VineEstS3.cohmolIndexΓ (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) +
        (Famb.VineEstS3.step3DΓ hM9 (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (sourceLayer_isLayering a)
          (Famb.VineEstS3.canonBadKindΓ hM9 (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a))
          (qOutOf a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (unitBlk Pg.γ hMa a.totalSigma j).upper
            (unitBlk Pg.γ hMa a.totalSigma j).lower (regionOf (unitBlk Pg.γ hMa a.totalSigma j)))
          (fun _ => (0 : Mom (PB Pg C).d)) (0 : Mom (PB Pg C).d)).M₁)
      (fun j => (Finset.univ.filter fun i : Fin (unitN a.totalSigma j) =>
        (Famb.VineEstS2.assemblyShapeΓ hM9 (sourceAssembly Pg.γ a j)).nor i = false).card)
      (fun i j => regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk Pg.γ hMa a.totalSigma j)) (sourceLayer Pg.γ a)
        (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)))
      ?_ ?_ ?_ N s ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
    · intro D' hD z
      exact (VineA.PrescribedPrimeGarden.normalizedPiece_gapIndicator a D' hD (lt_of_lt_of_le zero_lt_one hL1).ne' _ _ base roots z).trans
        (selSkC_ite a _ _ _ (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z)
    · intro i s'
      generalize (profileShape Pg.γ a).iota a.prime.prime.1 hGplain s' = s0
      unfold slotLeaf
      rcases s0 with p' | b
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    · intro i j
      exact WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)
    · intro i j
      have hb0 : 0 ≤ ((U.b i : NNReal) : ℝ) := NNReal.coe_nonneg _
      refine ⟨?_, le_of_eq ?_⟩
      · unfold unitMass
        have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
          mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
        exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
          (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ hb0)
      · unfold unitMass
        rw [nor_card_eq hM9 (sourceAssembly Pg.γ a j)]
        simp only [neg_mul]
    · intro i ξ
      have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
      have hordg : (a.prime.data.garden a.prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
        rw [a.prime.gardenEq, hordN]; exact hNmax
      obtain ⟨H, Mh, hsum, hHk, hprod⟩ := unit_hinge_data (PB Pg C) hV hM9 hgate hinc hd1 hη hη6 E.hη hC1ge hδ hL1 hw hp a
        hcan hordg tt base roots (U.h i) (U.b i) (NNReal.coe_nonneg _) (fun q j j' hq => hb i q j j' hq)
        (modLam (fun s => (fam i).m s (ξ s)) ((profileShape Pg.γ a).route a.prime.prime.1 hGplain))
      refine ⟨H, Mh, hsum, hHk, ?_⟩
      rw [hprod]
      have hM0 : ∀ j, 0 ≤ unitMass (PB Pg C) hM9 (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a)
          (sourceLayer_isLayering a) (U.b i) := fun j => by
        unfold unitMass
        have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
          mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
        exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
          (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
      have hpr : 0 ≤ ∏ j, unitMass (PB Pg C) hM9 (sourceAssembly Pg.γ a j) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a)
          (sourceLayer_isLayering a) (U.b i) := Finset.prod_nonneg fun j _ => hM0 j
      have hlam : 0 ≤ ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s))
          ((profileShape Pg.γ a).route a.prime.prime.1 hGplain) j : ℤ) : ℝ)|) ^ (6 * (PB Pg C).η ^ 6) :=
        Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
      have hch := ChinF_spec Pg.d Pg.η E.hη0
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hpr) hlam
      exact pow_le_pow_left₀ hch (le_max_right _ _) _
    · have hprodeq : ∀ i : U.ι, (∏ t, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (sourceLayer_isLayering a)
          (fun _ => U.b i) ((profileShape Pg.γ a).iota a.prime.prime.1 hGplain t)) *
          ∏ j, regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk Pg.γ hMa a.totalSigma j)) (sourceLayer Pg.γ a)
            (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)) =
          leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [leaf_prod_split (profileShape Pg.γ a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
          (sourceLayer Pg.γ a) (sourceLayer_isLayering a) (U.b i), sourceLayer_reconstructs a]
      calc _ ≤ ∑ i : U.ι, leafSizeProduct a.layered (fun _ => U.b i) := Finset.sum_le_sum fun i _ => by
            have hnn : 0 ≤ leafSizeProduct a.layered (fun _ => U.b i) :=
              Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
            exact (mul_le_of_le_one_left (hnn.trans (hprodeq i).symm.le) (hsgn i)).trans (hprodeq i).le
        _ = U.toLF.size a.layered := rfl
        _ ≤ s := hsize a.layered haA
    · have hn : N - a.prime.skeleton.order = a.prime.data.size := by omega
      exact exponent_order (profileShape Pg.γ a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain N hn
        (by omega)
    · have h1 := gsk_bound (profileShape Pg.γ a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
        (sourceLayer Pg.γ a) (sourceLayer_isLayering a) a.totalSigma (B₀ := sourceAssembly Pg.γ a)
        (hcov_units hMa a.totalSigma)
        (fun v => sourceLayer Pg.γ a (a.prime.data.coreBranch a.prime.prime.1 v).toNode) (fun v => rfl)
      have h2 := gsk_of_spec (γ := Pg.γ) a.prime.data a.prime.prime.1 (sourceLayer Pg.γ a) (sourceLayer_isLayering a) a.layered
        (sourceLayer_reconstructs a) a.prime.decodes a.totalSigma
      refine le_trans (le_of_eq h2) (le_trans h1 (le_of_eq ?_))
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Famb.VineEstS4.step3D_M1Γ]
      rfl
    · refine le_trans (le_of_eq (normalizedPiece_bsk a _))
        (bsk_bound hM9 a.totalSigma (sourceAssembly Pg.γ a) (hcov_units hMa a.totalSigma))
    · exact le_of_eq ((card_hinges (profileShape Pg.γ a) (unitBlk_disj hMa a.totalSigma)).symm.trans
        (congrArg Finset.card (profileShape_hinges a)))
    · exact card_units_le_order (profileShape Pg.γ a) (unitBlk_disj hMa a.totalSigma)
    · rfl
  subst ha
  exact key

end VineCase

end WaveTurbulence.GammaLow.Fama.Represents
