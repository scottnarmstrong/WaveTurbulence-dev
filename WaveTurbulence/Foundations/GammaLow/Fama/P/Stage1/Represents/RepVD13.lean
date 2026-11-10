/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVD13` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstGamma
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepKC1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU7
public import WaveTurbulence.Foundations.Stage1.Represents.RepE1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN10
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD13
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNU4
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVC1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVC3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD10
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD6
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD7
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD9
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE3
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedGapIndicator
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
# S2 REPRESENTS, session 12: the hinge data of the units of the representative (B4)

`g2_unitsN`: `g2_units` against the successor `NormalizedSplice` designations.
`unit_hinge_data`: `hinge_units_const` instantiated at the aligned unit assembly of the representative `a`, with the common
selection `selSkC`, the leaf flags of `G_sb`, and the hypotheses `hcont`, `hind`, G1, G2 discharged.
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
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

open scoped Classical in
theorem g2_unitsN (P : WTParams) {w : ℕ} {S : Garden w} (hM : S.molecule.IsMolecule) (hS : S.IsPlain)
    (σ : Prescription S) (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ))
    (D : SplicedKernelData (stSt γ S σ).G P.d) (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecification γ S σ)
    {n₀ : Fin (unitBlocks γ S σ).length → ℕ}
    {B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ S (regionOf (unitBlk γ hM σ j)) (n₀ j)} (hM9 : Famb.NormalChartSupply γ)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    ∀ κ : GenDecoration (stSt γ S σ).G P.d roots 0,
      splicedGapIndicator (stSt γ S σ).G D P.L P.γ P.η base κ.1 ≠ 0 →
      ∀ j (c : Fin 4 → Fin P.d → ℤ),
        (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (S.sign (unitBlk γ hM σ j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape γ hM σ).hmom (unitBlk_disj hM σ) j i))) ∈
          outSet (unitD hM9 (B₀ j) RD hG layer hLayer
            (sumintBoundary (S.sign (unitBlk γ hM σ j).upper.toNode) (fun i => latPt P.d (c i))) base) P.L P.γ P.η :=
  fun κ hκ j c hball =>
    mem_outSet_of_gsbN hM hS σ hL P.γ P.η base roots κ D hD hκ j c hball _ rfl rfl


theorem gap_value_eq_gapValue {R : ℕ} (a : VineA.PrescribedPrimeGarden γ (2 * R)) {d : ℕ} (L γ' η : ℝ) (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration a.fullProfile.piece.gap.garden d roots 0) :
    a.fullProfile.piece.gap.value d L γ' η hL base roots z =
      VineA.NormalizedSplice.gapValue γ a.prime.skeleton a.totalSigma L γ' η base z.1 := rfl

/-- The hinge-data constant of `hinge_units_const`, as a function of `(d, η)`. -/
noncomputable def ChinF (d : ℕ) (η : ℝ) : ℝ :=
  if h : 0 ≤ η then (hinge_units_const d η h).choose else 0

theorem ChinF_spec (d : ℕ) (η : ℝ) (h : 0 ≤ η) : 0 ≤ ChinF d η := by
  unfold ChinF
  rw [dif_pos h]
  exact (hinge_units_const d η h).choose_spec.1

open scoped Classical in
theorem unit_hinge_data (P : WTParams) [Fact (P.γ ≤ 1 / 2)] (hV : Famb.VineEstGammaHalfMK P) (hM9 : Famb.NormalChartSupply P.γ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (a : VineA.PrescribedPrimeGarden P.γ (2 * R)) (hcan : IsCanonGC (p + 1) a.layered)
    (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hp' : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (bb : ℝ) (hbb : 0 ≤ bb)
    (hB : ∀ q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (hp' q j j') ≤ ENNReal.ofReal bb)
    (lam : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length) P.d)
      (Mh : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp (a.normalizedPiece P.d) tt base roots
        (selSkC P.γ a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots)
        ((profileShape P.γ a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        ((profileShape P.γ a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        (fun j => unitHk P p (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
          (sourceLayer_isLayering a)
          (unitProfile (unitBlk P.γ (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) hp' j) base (lam j)) H ∧
      ∏ j, Mh j = ChinF P.d P.η ^ Fintype.card (Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length) *
        (∏ j, unitMass P hM9 (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
          (sourceLayer_isLayering a) bb) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hspec := (hinge_units_const P.d P.η hη0.le).choose_spec
  have hChin : ChinF P.d P.η = (hinge_units_const P.d P.η hη0.le).choose := by
    unfold ChinF; rw [dif_pos hη0.le]
  rw [hChin]
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
      (sourceLayer_isLayering a)) := by rw [sourceLayer_reconstructs]; exact hcan
  have hordS : a.prime.skeleton.order ≤ P.N (p + 1) ^ 4 := by
    have := a.prime.data.decoded_order a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)
    omega
  have hcl : ∀ j : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length,
      clLocalOrder1 (regionOf (unitBlk P.γ hMa a.totalSigma j)) ≤ P.N 1 ^ 4 := fun j =>
    clLocalOrder1_le_N1 P _ hordS
  have hh' : ∀ j : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length, ∀ r ≤ p,
      SNormR (40 * P.d) (40 * P.d) (unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j r) ≤ ENNReal.ofReal bb :=
    fun j r hr => hB r _ _ hr
  have hLay : (a.normalizedPiece P.d).layer = (stSt P.γ a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)) := by
    funext c
    show RegRed.coreLayer a.layered a.prime.data a.prime.prime.1 a.prime.decodes ((stSt P.γ a.prime.skeleton a.totalSigma).M.ob c) = _
    rw [coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes]
    exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a) _ rfl _ _).symm
  have hG1 := g1_units P hMa a.totalSigma hM9 (B₀ := sourceAssembly P.γ a) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
    (sourceLayer_isLayering a) base tt roots (selSkC P.γ a P.L P.γ P.η hL0.ne' base roots)
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i)))
    (fun j c hc => qOut_one_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
      (sourceLayer_isLayering a) c hc)
    (fun j c hc => qOut_two_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
      (sourceLayer_isLayering a) c hc)
    (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a))
  let D' : SplicedKernelData (stSt P.γ a.prime.skeleton a.totalSigma).G P.d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      VineA.NormalizedSplice.gapSpecification P.γ a.prime.skeleton a.totalSigma, fun _ => 0, fun _ => 0⟩
  have hG2 : ∀ κ : GenDecoration (stSt P.γ a.prime.skeleton a.totalSigma).G P.d roots 0,
      selSkC P.γ a P.L P.γ P.η hL0.ne' base roots κ → ∀ (j : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length)
        (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape P.γ hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) -
        latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape P.γ hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) ∈
          outSet (unitD hM9 (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base) P.L P.γ P.η := by
    intro κ hκ j c hball
    refine g2_unitsN P hMa a.prime.prime.1 a.totalSigma hL0.ne' base roots D' rfl (B₀ := sourceAssembly P.γ a) hM9
      a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a) κ ?_ j c hball
    have hD' : D'.gapSpecification = VineA.NormalizedSplice.gapSpecification P.γ a.prime.skeleton a.totalSigma := by
      simp only [D']
    have h1 := VineA.NormalizedSplice.gapValue_eq_indicator a.totalSigma D' hD' P.L P.γ P.η base κ.1
    have h2 : VineA.NormalizedSplice.gapValue P.γ a.prime.skeleton a.totalSigma P.L P.γ P.η base κ.1 = 1 :=
      (gap_value_eq_gapValue a P.L P.γ P.η hL0.ne' base roots κ).symm.trans hκ
    rw [← h1, h2]
    exact one_ne_zero
  have hcont : ∀ (j : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length) (c : Fin 4 → Fin P.d → ℤ) (lam : ℤ),
      ∀ E ∈ outSet (unitD hM9 (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
        (sourceLayer_isLayering a)
        (sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
          (fun i => latPt P.d (c i))) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHk P p (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
          (sourceLayer_isLayering a) (unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j) base lam t
          (sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode) E))
          (cubeSet (unitD hM9 (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base).qOut) :=
    fun j c lam => unit_hcont hgate hinc hd1 hη0 hη6 hη2 hC1 hδ hL1 hw hp (unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j)
      bb (hh' j) a.prime.prime hM9 (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
      (sourceLayer_isLayering a) hcan' hord _ base lam
  have hind : ∀ (j : Fin (unitBlocks P.γ a.prime.skeleton a.totalSigma).length) (lam : ℤ) (t t' : Fin 3 → ℝ)
      (k : Fin 4 → Mom P.d), (∀ i, ¬ leafFlag P.γ hMa a.totalSigma j i → t i = t' i) →
      unitHk P p (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a)
        (unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j) base lam t k =
      unitHk P p (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a)
        (unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j) base lam t' k :=
    fun j lam t t' k ht => unitHk_hind P p (sourceAssembly P.γ a j) a.prime.data a.prime.prime.1 (sourceLayer P.γ a)
      (sourceLayer_isLayering a) _ base (leafFlag P.γ hMa a.totalSigma j) (leafFlag_zero hMa a.totalSigma j)
      (unit_hleaf1 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a)
        a.prime.prime j)
      (unit_hleaf2 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a)
        a.prime.prime j) lam t t' k ht
  obtain ⟨H, Mh, hsum, hHk, hprod⟩ := hspec.2 P rfl rfl hV (by linarith) hL0 hp a.prime.prime hM9 a.prime.data
    a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a) hcan' hord (B₀ := sourceAssembly P.γ a) hcl
    (fun j => unitProfile (unitBlk P.γ hMa a.totalSigma) hp' j) (fun _ => bb) (fun _ => hbb) hh'
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk P.γ hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i))) base (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1
        (sourceLayer P.γ a) (sourceLayer_isLayering a)) hcont (stSt P.γ a.prime.skeleton a.totalSigma).G tt roots
    (selSkC P.γ a P.L P.γ P.η hL0.ne' base roots)
    ((stSt P.γ a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)))
    ((stShape P.γ hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma))
    ((stShape P.γ hMa a.totalSigma).hclk (unitBlk_disj hMa a.totalSigma))
    (leafFlag P.γ hMa a.totalSigma)
    (fun j i => ((qOutOf a.prime.data a.prime.prime.1 (sourceLayer P.γ a) (unitBlk P.γ hMa a.totalSigma j).upper
      (unitBlk P.γ hMa a.totalSigma j).lower (regionOf (unitBlk P.γ hMa a.totalSigma j)) i : ℕ) : ℝ)) hind hG1 hG2 lam
  refine ⟨H, Mh, hsum, ?_, hprod⟩
  intro κ hκ τ hτ j c hball
  rw [hLay] at hτ
  exact hHk κ hκ τ hτ j c hball

end WaveTurbulence.GammaLow.Fama.Represents
