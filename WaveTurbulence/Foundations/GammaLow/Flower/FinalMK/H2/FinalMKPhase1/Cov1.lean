/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov1
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
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Book
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Book2
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.End
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.End2
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Inv
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Inv2
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Rel
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.Obj
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.Run1
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.State
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Bank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L8-H2 port of main `WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov1`** (sha256 in H2/COPIED-SHA256SUMS): only the declarations
that depend on the vine-family carrier, re-stated over L6's low run (`FinalCount.H`, `Src … Src.γL`,
`Step1.VineCut Src.γL`) and L8's marked carrier (`SurvivorDataG Src.γL`); everything else is main's,
by import. Low-range changes are marked `L8-H2:` at their site (H2-PLAN §0).

 # C1b1 MK-PHASE1 (12): transporting an object of `M₀` to the state along a renaming (coverage, part 1)

Main transports an **intact** object `U` to the state by the identity on atoms (`stateIso`, AsmTransport;
`stateObj_spec` AsmVN3; `singleVineVC_of_objVine` AsmVN13; `vineDataL_of_intact` LowChain22). A survivor with a
pending re-cut joint is present only through a renaming `π`: its shared joint `v` is represented by the remnant `r`
(`anc r = v`). `MatchA h U π` records what is needed: `π` is injective on `U.atoms`, lands in the present atoms, is a
section of `anc`, and every group dart of `U` is present. Then:

* `stateIsoA` : the induced isomorphism of `M₀` on `U.atoms` with the state on `U.atoms.image π`;
* `stateObjA_spec`: the transported object (atoms `image π`, joints `π U.upper`, `π U.lower`, darts through `down`);
* `singleVineVCA`: a vine object stays a single vine (main's proof with `π`);
* `vineDataA`: a vine cut of the state along the transported object, with fresh names, node darts in `U`, the joint
  pairs, the `SG` gap and the twin relation (main's `vineDataL_of_intact` with `π`).

For an intact object `π = id` (`matchA_of_intact`). Copied by source (sha256 in COPIED-SHA256SUMS). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.Flower.H2
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section transport
variable {M₀ : Molecule V D₀}

/-- An object `U` of `M₀` present in the state through the renaming `π`. -/
structure MatchA (h : HSt V D₀) (U : Src.Object Src.γL M₀) (π : V → V) : Prop where
  inj : Set.InjOn π U.atoms
  mem : ∀ a ∈ U.atoms, π a ∈ h.s.M.atoms
  anc : ∀ a ∈ U.atoms, h.anc (π a) = a
  lift : ∀ z : D₀, M₀.InGroup U.atoms z → ∃ y : h.s.D, h.s.down y = z

variable {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
  (hinj : ∀ c ∈ h.s.M.atoms, ∀ e ∈ h.s.M.atoms, h.anc c = h.anc e → c = e) {U : Src.Object Src.γL M₀} {π : V → V}
  (hm : MatchA h U π)
include hA hD hinj hm

/-- A present dart whose `M₀` atom lies in `U` sits at the renamed atom. -/
theorem MatchA.atom_eq {y : h.s.D} (hy : M₀.atom (h.s.down y) ∈ U.atoms) :
    h.s.M.atom y = π (M₀.atom (h.s.down y)) := by
  refine hinj _ (h.s.M.atom_mem y) _ (hm.mem _ hy) ?_
  rw [hm.anc _ hy, hA.atom]

theorem MatchA.group_lift {z : D₀} (hz : M₀.InGroup U.atoms z) :
    ∃ y : h.s.D, h.s.down y = z ∧ h.s.M.InGroup (U.atoms.image π) y := by
  obtain ⟨y, hy⟩ := hm.lift z hz
  have h1 : h.s.M.atom y = π (M₀.atom z) := by rw [MatchA.atom_eq hA hD hinj hm (hy ▸ hz.1), hy]
  have h2 : h.s.M.atom (h.s.M.mate y) = π (M₀.atom (M₀.mate z)) := by
    have hz2 : M₀.atom (h.s.down (h.s.M.mate y)) ∈ U.atoms := by rw [← hD.mate, hy]; exact hz.2
    rw [MatchA.atom_eq hA hD hinj hm hz2, ← hD.mate, hy]
  exact ⟨y, hy, by rw [h1]; exact Finset.mem_image_of_mem _ hz.1, by rw [h2]; exact Finset.mem_image_of_mem _ hz.2⟩

theorem MatchA.group_down {y : h.s.D} (hy : h.s.M.InGroup (U.atoms.image π) y) : M₀.InGroup U.atoms (h.s.down y) := by
  have key : ∀ c : V, c ∈ U.atoms.image π → h.anc c ∈ U.atoms := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hm.anc a ha]; exact ha
  refine ⟨?_, ?_⟩
  · rw [hA.atom]; exact key _ hy.1
  · rw [hD.mate, hA.atom]; exact key _ hy.2

/-- **The induced isomorphism along the renaming** (main's `stateIso` with `π`). -/
noncomputable def stateIsoA : RedSplice.InducedIso M₀ h.s.M U.atoms (U.atoms.image π) where
  π := π
  inj := hm.inj
  img := rfl
  sub := fun c hc => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc; exact hm.mem a ha
  e :=
    { toFun := fun x => ⟨Classical.choose (MatchA.group_lift hA hD hinj hm x.2),
        (Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)).2⟩
      invFun := fun y => ⟨h.s.down y.1, MatchA.group_down hA hD hinj hm y.2⟩
      left_inv := fun x => Subtype.ext (Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)).1
      right_inv := fun y => Subtype.ext (hA.inj
        (Classical.choose_spec (MatchA.group_lift hA hD hinj hm (MatchA.group_down hA hD hinj hm y.2))).1) }
  atom_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    show h.s.M.atom (Classical.choose (MatchA.group_lift hA hD hinj hm x.2)) = π (M₀.atom x.1)
    rw [MatchA.atom_eq hA hD hinj hm (by rw [hx.1]; exact x.2.1), hx.1]
  mate_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    have hmx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm
      (show M₀.InGroup U.atoms (M₀.mate x.1) from ⟨x.2.2, by simpa [M₀.mate_mate] using x.2.1⟩))
    have e2 : h.s.down (h.s.M.mate (Classical.choose (MatchA.group_lift hA hD hinj hm x.2))) = M₀.mate x.1 := by
      rw [← hD.mate, hx.1]
    exact hA.inj (hmx.1.trans e2.symm)
  out_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    show h.s.M.out (Classical.choose (MatchA.group_lift hA hD hinj hm x.2)) = M₀.out x.1
    rw [← hD.out, hx.1]

theorem stateIsoA_e {x : D₀} (hx : M₀.InGroup U.atoms x) :
    h.s.down ((stateIsoA hA hD hinj hm).e ⟨x, hx⟩).1 = x :=
  (Classical.choose_spec (MatchA.group_lift hA hD hinj hm hx)).1

/-- **The transported object** (main's `stateObj_spec` with `π`). -/
theorem stateObjA_spec :
    ∃ Ũ : Src.Object Src.γL h.s.M, Ũ.atoms = U.atoms.image π ∧ Ũ.upper = π U.upper ∧ Ũ.lower = π U.lower ∧
      (∀ z : h.s.D, Ũ.ContainsDart z ↔ U.ContainsDart (h.s.down z)) ∧
      ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = U.atoms.image π → FinalCount.H.ObjVine M₀ U → Step1.SingleVineVCGamma K' := by
  let I := stateIsoA hA hD hinj hm
  refine ⟨I.mapObjL U subset_rfl, rfl, rfl, rfl, fun z => ?_, ?_⟩
  · constructor
    · intro hz
      have hg := FinalCount.H.containsDart_inGroup _ hz
      have hg' : h.s.M.InGroup (U.atoms.image π) z := hg
      have hx := MatchA.group_down hA hD hinj hm hg'
      have e : (I.e ⟨h.s.down z, hx⟩).1 = z := by
        apply hA.inj
        exact stateIsoA_e hA hD hinj hm hx
      have := (I.containsDart_mapL U subset_rfl hx).mp (by rw [e]; exact hz)
      exact this
    · intro hz
      have hx := FinalCount.H.containsDart_inGroup U hz
      have e : (I.e ⟨h.s.down z, hx⟩).1 = z := by
        apply hA.inj
        exact stateIsoA_e hA hD hinj hm hx
      have := (I.containsDart_mapL U subset_rfl hx).mpr hz
      rwa [e] at this
  · intro K' hat hov
    obtain ⟨A, u, l, sh⟩ := U
    simp only at hat hov
    have hat' : K'.C.atoms = (I.mapObjL ⟨A, u, l, sh⟩ subset_rfl).atoms := hat
    have hjoint : ({K'.C.upper, K'.C.lower} : Finset V) = {π u, π l} :=
      FinalCount.H.object_joints_eq K'.C (I.mapObjL ⟨A, u, l, sh⟩ subset_rfl) hat'
    cases sh with
    | vc h0 =>
      rcases FinalCount.H.object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
      · have hX : Src.IsSomeVine Src.γL M₀ A u l := Src.isSomeVine_γL_iff.mpr hov
        have hv : Src.IsSomeVine Src.γL h.s.M (A.image π) (π u) (π l) := I.isVineS hX
        unfold Step1.SingleVineVCGamma
        rw [hsh']
        exact FinalCount.H.isSomeVine_atoms_congr hat.symm (FinalCount.H.isSomeVine_orient K'.ab_ne hjoint hv)
      · exact (FinalCount.H.not_vc_hyper_atoms (U := I.mapObjL ⟨A, u, l, .vc h0⟩ subset_rfl) (U' := K'.C) ⟨_, rfl⟩ ⟨R', hsh'⟩
          hat'.symm).elim
    | hyper R =>
      rcases FinalCount.H.object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
      · exact (FinalCount.H.not_vc_hyper_atoms (U := K'.C) (U' := I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl) ⟨h', hsh'⟩ ⟨_, rfl⟩
          hat').elim
      · have he : M₀.InGroup A R.added := RedSplice.inGroup_of_ends R.ends_eq R.adjoint.1.2.1 R.adjoint.1.2.2.1
        obtain ⟨Rt, hRt, hRta⟩ : ∃ Rt, (I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl).shape = .hyper Rt ∧
            Rt.added = (I.e ⟨R.added, he⟩).1 := ⟨_, rfl, rfl⟩
        have hX : Src.IsSomeVine Src.γL (M₀.eraseBond R.added) A u l := Src.isSomeVine_γL_iff.mpr hov
        have hv : Src.IsSomeVine Src.γL (h.s.M.eraseBond (I.e ⟨R.added, he⟩).1) (A.image π) (π u) (π l) :=
          (I.eraseE R.added he).isVineS hX
        unfold Step1.SingleVineVCGamma
        rw [hsh']
        by_cases h1 : R'.added = (I.e ⟨R.added, he⟩).1
        · exact FinalCount.H.isSomeVine_atoms_congr hat.symm
            (FinalCount.H.isSomeVine_orient K'.ab_ne hjoint (FinalCount.H.isSomeVine_eraseBond_congr h1.symm hv))
        · by_cases h2 : R'.added = h.s.M.mate (I.e ⟨R.added, he⟩).1
          · have hB : A.image π ⊆ h.s.M.atoms := I.sub
            have hv2 := (eraseMateIso h.s.M (I.e ⟨R.added, he⟩).1 (A.image π) hB).isVineS hv
            exact FinalCount.H.isSomeVine_atoms_congr hat.symm
              (FinalCount.H.isSomeVine_orient K'.ab_ne hjoint (FinalCount.H.isSomeVine_eraseBond_congr h2.symm hv2))
          · refine Src.isSomeVine_γL_iff.mpr
              (FinalCount.H.hyper_other_isSomeVine (I.mapObjL ⟨A, u, l, .hyper R⟩ subset_rfl) K'.C hat'.symm hRt hsh' ?_)
            rw [hRta]
            exact fun h => h.elim h1 h2

end transport

end WaveTurbulence.GammaLow.Flower.H2
