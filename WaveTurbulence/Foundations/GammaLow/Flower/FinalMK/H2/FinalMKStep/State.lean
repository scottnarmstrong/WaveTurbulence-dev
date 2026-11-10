/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FinalMKStep.State
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmConn1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmConn2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGCn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGHost2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGReg1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGReg2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGTrans
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGarden2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGarden3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmHmem
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmHmemShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmLadderHered
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Dev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1H
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Pot
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Rho
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhased
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPrefix
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmRegMol
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmRun3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmS4Shape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTerm15c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTerm15d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTerm16c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTopClass2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmUnsel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapGarden
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapSubpro
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.FinalCountClose
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3AdmRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Elig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Ex1New
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3SrcGaps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5a
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TripleGe4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TripleThm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineObj4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL16
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL23
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL25
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL26
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL29
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GM08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV06
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV09
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain22
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain23
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain24
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain25
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain26
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain30
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain38
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain40
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain42
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain43
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain44
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain45
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain46
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenCn3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopFacts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopMain3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenOne
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenSplit3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGlue
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Disj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproChainSplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproCollDisj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproInterleaved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproOneJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeC1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeConn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeRem
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeStraddle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproStep1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproSupportA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.VrHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapAdjointClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVBlockBranchEquality
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMixedRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryShapes
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapProperness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperJointPairShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperMixedRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperOrdinaryBothRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperOrdinaryMissingRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperOrdinaryRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineOrdinarySplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGMixedRemovalVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalSingle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSplitJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInHyperLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCVineLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKDefs.Count
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Bank
/-! **L8-H2 port of main `WaveTurbulence.Foundations.Flower.FinalMKStep.State`** (sha256 in H2/COPIED-SHA256SUMS): only the declarations
that depend on the vine-family carrier, re-stated over L6's low run (`FinalCount.H`, `Src … Src.γL`,
`Step1.VineCut Src.γL`) and L8's marked carrier (`SurvivorDataG Src.γL`); everything else is main's,
by import. Low-range changes are marked `L8-H2:` at their site (H2-PLAN §0).

 # C1a SURV-STEP (2): the state after a re-cut (`vineStG` at an `α/β` joint of degree `2`)

Main's `vineStG s K` (GL4) cuts both joints of the object (the half in the object keeps the class `β`, the other half
gets `jcls`: a ghost at a degree-`2` joint) and deletes the object and the ghosts. Main proves its invariants for
`ε` joints (`Inv.vineStG`, `HGap.vinePostG`, `apProd_vineStG`, `vBeta_vineStG`). Here the joints may also be `α/β`
remnants of degree `2` (the re-cut joints of o75 75-F2):

* `Inv.vineStRC`: the index drops by `jeps K` (the `ε` joints of degree `2`); an `α/β` joint of degree `2` has
  `contrib = 0` and its ghost half has `contrib = 0`, so it does not move the index;
* `HGap.vinePostRC` (an `α/β` joint of degree `2` is cut by main's `HGap.cut_two`), `invL_stepRC` (C1a target 3,
  `InvLStepRC`);
* the general product formula `prod_vineStG'` and its consequences: the label refund
  `apProd s ≤ apProd (vineStG s K)` (`apProd_le_vineStRC`), `vBeta_vineStRC`, `numComponents_vineStRC`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.Flower.H2
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The number of `ε` joints of degree `2` of the object: the index drop of the re-cut step. -/
noncomputable def jeps {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) : ℕ := jepsAt s K.C.upper + jepsAt s K.C.lower

section inv
variable {s : St.{u} V D₀} {R : ℕ}

/-- **The index along a re-cut** (`Inv.vineStGL` with re-cut joints): it drops by `jeps K`. -/
theorem Inv.vineStRC (hI : Inv R s) (K : Step1.VineCut Src.γL s.M) (hu : RCJoint s K.C.upper) (hl : RCJoint s K.C.lower) :
    ∃ R', R' + jeps K = R ∧ Inv R' (FinalCount.H.vineStG s K) := by
  obtain ⟨R1, e1, hI1⟩ := Inv.cutJRC hI K.cut_a hu (FinalCount.H.two_le_deg_upper K)
  have hdl : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
  have hlowc : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cls K.C.lower = s.cls K.C.lower := by
    show Function.update (Function.update s.cls K.C.upper .beta) K.fa (jcls s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]
  have hl' : RCJoint (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.C.lower := by
    unfold RCJoint
    rw [hlowc]
    show s.cls K.C.lower = .eps ∨ ((s.cls K.C.lower).IsAB ∧ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2)
    rw [hdl]; exact hl
  obtain ⟨R2, e2, hI2⟩ := Inv.cutJRC hI1 (s := s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper))
    K.cut_b hl' (by show 2 ≤ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower; rw [hdl]; exact FinalCount.H.two_le_deg_lower K)
  have hj2 : jcls (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).M K.C.lower = jcls s.M K.C.lower :=
    jcls_congr _ _ hdl
  rw [hj2] at hI2
  have e2' : jepsAt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)) K.C.lower = jepsAt s K.C.lower := by
    unfold jepsAt
    rw [hlowc]
    show (if s.cls K.C.lower = .eps ∧ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2 then 1 else 0) = _
    rw [hdl]
  rw [e2'] at e2
  refine ⟨R2, by unfold jeps; omega, ?_⟩
  refine hI2.delSt _ (FinalCount.H.VineKeep.closed K) ?_
  intro a ha hna
  have hna' : a ∈ K.C.atoms ∨ (a = K.fa ∧ s.M.deg K.C.upper = 2) ∨ (a = K.fb ∧ s.M.deg K.C.lower = 2) := by
    unfold FinalCount.H.VineKeep at hna
    by_contra hcon
    push Not at hcon
    exact hna ⟨hcon.1, fun h => hcon.2.1 h.1 h.2, fun h => hcon.2.2 h.1 h.2⟩
  have e_ua : K.C.upper ≠ K.fa := fun e => K.fa_fresh (e ▸ K.a_atom)
  have e_ub : K.C.upper ≠ K.fb := K.fb_ne_a.symm
  have e_ul : K.C.upper ≠ K.C.lower := K.ab_ne
  have e_lb : K.C.lower ≠ K.fb := fun e => K.fb_fresh (e ▸ K.b_atom)
  have hcl2 : ∀ b, ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).cls b = Function.update (Function.update (Function.update (Function.update s.cls K.C.upper .beta)
        K.fa (jcls s.M K.C.upper)) K.C.lower .beta) K.fb (jcls s.M K.C.lower) b := fun b => rfl
  have hdeg2 : ∀ b, ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).M.deg b = ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg b :=
    fun b => rfl
  show (((s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls s.M K.C.upper)).cutSt K.C.lower K.fb K.y₁ K.y₂ .beta
      (jcls s.M K.C.lower)).cls a).base = _
  rw [hcl2, hdeg2]
  rcases hna' with haC | ⟨hfa, hd2⟩ | ⟨hfb, hd2⟩
  · have haM : a ∈ s.M.atoms := Step1.objectAtoms_sub K.C haC
    have hfa : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
    have hfb : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
    by_cases h1 : a = K.C.upper
    · rw [h1, Function.update_of_ne e_ub, Function.update_of_ne e_ul, Function.update_of_ne e_ua, Function.update_self]
      rw [cut_deg_other K.cut_b e_ul e_ub, cut_deg_v s.M K.cut_a]; rfl
    · by_cases h2 : a = K.C.lower
      · rw [h2, Function.update_of_ne e_lb, Function.update_self]
        rw [cut_deg_v _ K.cut_b]; rfl
      · rw [Function.update_of_ne hfb, Function.update_of_ne h2, Function.update_of_ne hfa, Function.update_of_ne h1,
          cut_deg_other K.cut_b h2 hfb, cut_deg_other K.cut_a h1 hfa]
        have h4 := FinalCount.H.vine_interior_deg K hI.bounds haC h1 h2
        have hce' : s.cls a = .eps := by
          by_contra hne
          have := (hI.ab a haM hne).1; omega
        rw [hce', h4]; rfl
  · subst hfa
    have hne1 : K.fa ≠ K.fb := K.fa_ne_fb
    have hjc : jcls s.M K.C.upper = .ghost := by unfold jcls; rw [ite_eq_left hd2]
    rw [Function.update_of_ne hne1, Function.update_of_ne K.fa_ne_b, Function.update_self, hjc]
    rw [cut_deg_other K.cut_b K.fa_ne_b K.fa_ne_fb]
    have := cut_deg_v₂ K.cut_a
    rw [hd2] at this
    rw [show (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.fa = 0 by omega]; rfl
  · subst hfb
    have hjc : jcls s.M K.C.lower = .ghost := by unfold jcls; rw [ite_eq_left hd2]
    rw [Function.update_self, hjc]
    have := cut_deg_v₂ K.cut_b
    have hdl' : ((s.M.cut K.C.upper K.fa K.x₁ K.x₂)).deg K.C.lower = 2 := by rw [hdl]; exact hd2
    rw [hdl'] at this
    rw [show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb = 0 by omega]; rfl

end inv

section gap
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

/-- `HGap` after a re-cut (main's `HGap.vinePostGL` with re-cut joints). -/
theorem HGap.vinePostRC {h : HSt V D₀} (hG : HGap L w κ h) (hI : Inv R h.s) (K : Step1.VineCut Src.γL h.s.M)
    (hu : RCJoint h.s K.C.upper) (hl : RCJoint h.s K.C.lower) :
    HGap L w κ (h.vinePostGL K) := by
  have hdu := FinalCount.H.two_le_deg_upper K
  have hdl := FinalCount.H.two_le_deg_lower K
  have hup4 := deg_le_four _ (hI.bounds _ K.cut_a.1)
  have hlo : K.C.lower ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.b_mem
  have hlo4 := deg_le_four _ (hI.bounds _ hlo)
  have hlne : K.C.lower ≠ K.C.upper := K.ab_ne.symm
  have hlfa : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  have g1 := HGap.cutJRC hG (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a hu hup4 hdu h.alive
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hcl : (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).cls K.C.lower = h.s.cls K.C.lower := by
    show Function.update (Function.update h.s.cls K.C.upper .beta) K.fa (jcls h.s.M K.C.upper) K.C.lower = _
    rw [Function.update_of_ne hlfa, Function.update_of_ne hlne]
  have hdeg : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
    cut_deg_other K.cut_a hlne hlfa
  have hl' : RCJoint (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)) K.C.lower := by
    unfold RCJoint
    rw [hcl]
    show h.s.cls K.C.lower = .eps ∨ ((h.s.cls K.C.lower).IsAB ∧ (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = 2)
    rw [hdeg]; exact hl
  have g2 := HGap.cutJRC g1 (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    K.cut_b hl' (by show (h.s.M.cut _ _ _ _).deg _ ≤ 4; omega) (by show 2 ≤ (h.s.M.cut _ _ _ _).deg _; omega)
    (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
  have hj : jcls (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper)).M K.C.lower = jcls h.s.M K.C.lower :=
    jcls_congr _ _ hdeg
  rw [hj] at g2
  exact g2.delSt _ (FinalCount.H.VineKeep.closed K)

end gap

section invL
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

theorem HStepRC.data {C : FinalCount.H.CollData M₀} {h h' : HSt V D₀} (hs : HStepRC C L γ η w κ h h') :
    ∃ K : Step1.VineCut Src.γL h.s.M, RCJoint h.s K.C.upper ∧ RCJoint h.s K.C.lower ∧
      (h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps) ∧
      (pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂)) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      FinalCount.H.Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂) ∧ FinalCount.H.Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂) ∧
      h' = h.vinePostGL K := by
  cases hs with
  | vine K hu hl hrc htwin hsg hdu hdl => exact ⟨K, hu, hl, hrc, htwin, hsg, hdu, hdl, rfl⟩

/-- At least one joint of a re-cut is an `α/β` atom of degree `2`. -/
theorem rc_deg_two {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) (hu : RCJoint s K.C.upper) (hl : RCJoint s K.C.lower)
    (hrc : s.cls K.C.upper ≠ .eps ∨ s.cls K.C.lower ≠ .eps) :
    s.M.deg K.C.upper = 2 ∨ s.M.deg K.C.lower = 2 := by
  rcases hrc with h | h
  · exact Or.inl ((hu.resolve_left h).2)
  · exact Or.inr ((hl.resolve_left h).2)

/-- **The invariants along a re-cut**: the index drops by `jeps K ≤ 1`. -/
theorem InvL.stepRC {C : FinalCount.H.CollData M₀} {h h' : HSt V D₀} (hs : HStepRC C L γ η w κ h h')
    (hr : InvL M₀ R L γ η w κ h) :
    ∃ K : Step1.VineCut Src.γL h.s.M, ∃ R', R' + jeps K = R ∧ h' = h.vinePostGL K ∧ InvL M₀ R' L γ η w κ h' := by
  obtain ⟨K, hu, hl, -, htwin, hsg, -, -, rfl⟩ := HStepRC.data hs
  obtain ⟨R', e, hI⟩ := Inv.vineStRC hr.good.1 K hu hl
  exact ⟨K, R', e, rfl,
    { good := ⟨hI, FinalCount.H.clean_vineStG hr.good.2 K⟩
      hrec := hr.hrec.vinePostGL K htwin hsg
      gap := HGap.vinePostRC hr.gap hr.good.1 K hu hl
      comp := hr.comp.vineStGL K
      bal := hr.bal.vineStGL K
      rel := hr.rel.vineStGL K }⟩

end invL

section prod
variable (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M)

/-- **Products over the atoms after a re-cut** (main's `prod_vineStG` without the assumption that the removed object
contributes `1`): the post product times the object's product is the old product times the surviving halves. -/
theorem prod_vineStG' {α : Type*} [CommMonoid α] (F : Cls → α) :
    (∏ a ∈ (FinalCount.H.vineStG s K).M.atoms, F ((FinalCount.H.vineStG s K).cls a)) * ∏ a ∈ K.C.atoms, F (s.cls a) =
      (if s.M.deg K.C.lower = 2 then 1 else F .beta) * (if s.M.deg K.C.upper = 2 then 1 else F .beta) *
        ∏ a ∈ s.M.atoms, F (s.cls a) := by
  have hfa : K.fa ∉ s.M.atoms := K.fa_fresh
  have hfb : K.fb ∉ insert K.fa s.M.atoms := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact K.fa_ne_fb e.symm
    · exact K.fb_fresh h
  have hsub : K.C.atoms ⊆ s.M.atoms := fun a ha => Step1.objectAtoms_sub K.C ha
  rw [FinalCount.H.vineStG_atoms, Finset.prod_filter, Finset.prod_insert hfb, Finset.prod_insert hfa]
  have e1 : ∏ a ∈ s.M.atoms, (if FinalCount.H.VineKeep K a then F ((FinalCount.H.vineStG s K).cls a) else 1) =
      ∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), F (s.cls a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun a ha => ?_
    by_cases haC : a ∈ K.C.atoms
    · have : ¬ FinalCount.H.VineKeep K a := fun hk => hk.1 haC
      rw [ite_eq_right this, ite_eq_right (not_not.2 haC)]
    · have hk : FinalCount.H.VineKeep K a := by
        refine ⟨haC, ?_, ?_⟩
        · rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ ha)
        · rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ ha)
      rw [ite_eq_left hk, ite_eq_left haC, FinalCount.H.vineStG_cls_old s K haC ha]
  have h1 : s.M.atoms.filter (fun a => a ∈ K.C.atoms) = K.C.atoms := by
    ext a; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have e2 : ∏ a ∈ s.M.atoms, F (s.cls a) =
      (∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), F (s.cls a)) * ∏ a ∈ K.C.atoms, F (s.cls a) := by
    rw [← Finset.prod_filter_mul_prod_filter_not s.M.atoms (fun a => a ∈ K.C.atoms), h1, mul_comm]
  have hfaK : (if FinalCount.H.VineKeep K K.fa then F ((FinalCount.H.vineStG s K).cls K.fa) else 1) = if s.M.deg K.C.upper = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.upper = 2
    · have : ¬ FinalCount.H.VineKeep K K.fa := fun hk => hk.2.1 ⟨rfl, hd⟩
      rw [ite_eq_right this, ite_eq_left hd]
    · have hk : FinalCount.H.VineKeep K K.fa := ⟨fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h), fun ⟨_, h⟩ => hd h,
        fun ⟨e, _⟩ => K.fa_ne_fb e⟩
      rw [ite_eq_left hk, ite_eq_right hd, FinalCount.H.vineStG_cls_fa]; unfold jcls; rw [ite_eq_right hd]
  have hfbK : (if FinalCount.H.VineKeep K K.fb then F ((FinalCount.H.vineStG s K).cls K.fb) else 1) = if s.M.deg K.C.lower = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.lower = 2
    · have : ¬ FinalCount.H.VineKeep K K.fb := fun hk => hk.2.2 ⟨rfl, hd⟩
      rw [ite_eq_right this, ite_eq_left hd]
    · have hk : FinalCount.H.VineKeep K K.fb := ⟨fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h), fun ⟨e, _⟩ => K.fa_ne_fb e.symm,
        fun ⟨_, h⟩ => hd h⟩
      rw [ite_eq_left hk, ite_eq_right hd, FinalCount.H.vineStG_cls_fb]; unfold jcls; rw [ite_eq_right hd]
  rw [hfaK, hfbK, e1, e2]
  simp only [mul_assoc]

end prod

end WaveTurbulence.GammaLow.Flower.H2
