/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Run1
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
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.State
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Bank
/-! **L8-H2 port of main `WaveTurbulence.Foundations.Flower.FinalMKStep.Run1`** (sha256 in H2/COPIED-SHA256SUMS): only the declarations
that depend on the vine-family carrier, re-stated over L6's low run (`FinalCount.H`, `Src … Src.γL`,
`Step1.VineCut Src.γL`) and L8's marked carrier (`SurvivorDataG Src.γL`); everything else is main's,
by import. Low-range changes are marked `L8-H2:` at their site (H2-PLAN §0).

 # C1a SURV-STEP (5): the LOW run with re-cuts, part 1 (`HRunLE.inv`, `HRunLE.final`, `HRunLE.cycles`)

Copy-thread of main's G3-LOWDEG run layer (GL6 `HRunL.inv`, GL8 `HStep1L.aux`, GL9 `HRunL.inv3`/`HRunL.final`, GL10
`desig_pairL`/`HRunL.cycles`; sha256 in COPIED-SHA256SUMS) from `HRunL` to the probe's `HRunLE` (Step 1 = `HStep1L` or
the re-cut `HStepRC`). The proofs are main's, with one new case per Step-1 induction (the re-cut, through
`InvL.stepRC` and main's `vinePostG` lemmas).

The only other change: main's run lemmas take the whole `SubproOblG` but read only its field `hingeSG`. Survivors
change `SubproOblG` (C1b's `SubproOblGMK`) but not this field, so the copies take `HingeSG` (`SubproOblG.hingeSGP`,
`SubproOblGMK.hingeSGP`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.GammaLow.Flower.H2
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- `subpro` (5) at the hinges: the only field of `SubproOblG` read by the run layer. -/
def HingeSG (C : FinalCount.H.CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop :=
  ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAtM M₀ v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG)

theorem SubproOblGMK.hingeSGP {C : FinalCount.H.CollData M₀} {m : ℕ} {E : Fin m → Src.Object Src.γL M₀} (obl : SubproOblGMK C E L γ η w κ) :
    HingeSG C L γ η w κ := obl.hingeSG

variable {h h' : HSt V D₀}

/-! ### One Step-1 step with re-cuts -/

theorem InvL.step1LE {C : FinalCount.H.CollData M₀} (hs : HStep1LE C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h' := by
  cases hs with
  | base hs => exact hr.step1LL hs
  | recut hs =>
    obtain ⟨K, R', e, -, hI⟩ := InvL.stepRC hs hr
    exact ⟨R', by omega, hI⟩

/-- `DesRecN` along a re-cut (main's `DesRecN.vineD1`, GL8, with the `HStepRC` constructor). -/
theorem DesRecN.recut {C : FinalCount.H.CollData M₀} (hD : FinalCount.H.DesRecN C h) (hs : HStepRC C L γ η w κ h h') : FinalCount.H.DesRecN C h' := by
  cases hs with
  | vine K' hu' hl' hrc' htwin' hsg' hdu hdl =>
    have n1 : K'.fa ≠ K'.fb := K'.fa_ne_fb
    have n2 : K'.fa ≠ K'.C.lower := K'.fa_ne_b
    have n3 : K'.fb ≠ K'.C.upper := K'.fb_ne_a
    have n4 : K'.fa ≠ K'.C.upper := fun e => K'.fa_fresh (e ▸ K'.a_atom)
    have n5 : K'.fb ≠ K'.C.lower := fun e => K'.fb_fresh (e ▸ K'.b_atom)
    intro j p vis hj
    by_cases e1 : j = K'.fb
    · subst e1
      simp [FinalCount.H.HSt.vinePostGL, WaveTurbulence.FinalCountG3.HSt.vinePostGL, Function.update_apply, n1.symm, n5, n3] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdl
    by_cases e2 : j = K'.C.lower
    · subst e2
      simp [FinalCount.H.HSt.vinePostGL, WaveTurbulence.FinalCountG3.HSt.vinePostGL, Function.update_apply, e1, n2.symm, n5.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n2.symm, n5.symm] using hdl
    by_cases e3 : j = K'.fa
    · subst e3
      simp [FinalCount.H.HSt.vinePostGL, WaveTurbulence.FinalCountG3.HSt.vinePostGL, Function.update_apply, e1, e2, n1, n2, n4] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdu
    by_cases e4 : j = K'.C.upper
    · subst e4
      simp [FinalCount.H.HSt.vinePostGL, WaveTurbulence.FinalCountG3.HSt.vinePostGL, Function.update_apply, e1, e2, e3, n3.symm, n4.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n3.symm, n4.symm] using hdu
    · simp [FinalCount.H.HSt.vinePostGL, WaveTurbulence.FinalCountG3.HSt.vinePostGL, Function.update_apply, e1, e2, e3, e4] at hj ⊢
      exact hD j p vis hj

/-- The auxiliary invariants along a Step-1 step with re-cuts (main's `HStep1L.aux`, GL8). -/
theorem HStep1LE.aux {C : FinalCount.H.CollData M₀} (hs : HStep1LE C L γ η w κ h h') (ha : FinalCount.H.RunAux M₀ C h) : FinalCount.H.RunAux M₀ C h' := by
  cases hs with
  | base hs => exact hs.aux ha
  | recut hs =>
    obtain ⟨hdp, hA, hD⟩ := ha
    obtain ⟨K, -, -, -, -, -, -, -, rfl⟩ := HStepRC.data hs
    exact ⟨hdp.vinePostGL hA.inj K, hA.vinePostGL K, DesRecN.recut hD hs⟩

/-- `EpsLe` along a Step-1 step with re-cuts (main's `HStep1L.epsLe`, GL11). -/
theorem HStep1LE.epsLe {C : FinalCount.H.CollData M₀} (hs : HStep1LE C L γ η w κ h h') : EpsLe h.s h'.s := by
  cases hs with
  | base hs => exact hs.epsLe
  | recut hs =>
    obtain ⟨K, -, -, -, -, -, -, -, rfl⟩ := HStepRC.data hs
    exact FinalCount.H.EpsLe.vineStGL K

/-! ### The run invariants (GL6, GL9, GL11) -/

/-- **The invariants along a run of the LOW case with re-cuts** (main's `HRunL.inv`, GL6). -/
theorem HRunLE.inv {C : FinalCount.H.CollData M₀} {h₀ hf : HSt V D₀} (hr : HRunLE C L γ η w κ h₀ hf)
    (h0 : InvL M₀ R L γ η w κ h₀) : ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, -, a2, -, a3, -, a4, -, a5, -⟩ := hr
  let P : HSt V D₀ → Prop := fun h => ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → ∀ R', InvL M₀ R' L γ η w κ a →
      ∃ R'', R'' ≤ R' ∧ InvL M₀ R'' L γ η w κ b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → P a → P b := by
    intro S hS a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih =>
      obtain ⟨R', hR', hI⟩ := ih
      obtain ⟨R'', hR'', hI''⟩ := hS _ _ hs R' hI
      exact ⟨R'', hR''.trans hR', hI''⟩
  have p0 : P h₀ := ⟨R, le_rfl, h0⟩
  exact key (fun a b hs R' hI => ⟨R', le_rfl, hI.step4 hs⟩) a5
    (key (fun a b hs R' hI => ⟨R', le_rfl, hI.step3 hs.toHStep3⟩) a4
    (key (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) a3
    (key (fun a b hs R' hI => hI.stepD3'L hs) a2
    (key (fun a b hs R' hI => InvL.step1LE hs hI) a1 p0))))

/-- The invariants after Step 1 (main's `HRunL.inv1`, GL11). -/
theorem HRunLE.inv1 {C : FinalCount.H.CollData M₀} {h₀ h₁ : HSt V D₀}
    (a1 : Relation.ReflTransGen (HStep1LE C L γ η w κ) h₀ h₁) (h0 : InvL M₀ R L γ η w κ h₀) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h₁ := by
  let P : HSt V D₀ → Prop := fun h => ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h
  have : ∀ {a b : HSt V D₀}, Relation.ReflTransGen (HStep1LE C L γ η w κ) a b → P a → P b := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih =>
      obtain ⟨R', hR', hI⟩ := ih
      obtain ⟨R'', hR'', hI''⟩ := InvL.step1LE hs hI
      exact ⟨R'', hR''.trans hR', hI''⟩
  exact this a1 ⟨R, le_rfl, h0⟩

/-- The state after Step 2 satisfies the invariants with some index `≤ R` (main's `HRunL.inv3`, GL9). -/
theorem HRunLE.inv3 {C : FinalCount.H.CollData M₀} {h₀ h₃ : HSt V D₀} {h₁ h₂ : HSt V D₀}
    (a1 : Relation.ReflTransGen (HStep1LE C L γ η w κ) h₀ h₁)
    (a2 : Relation.ReflTransGen (FinalCount.H.HStepD3 C L γ η w κ) h₁ h₂)
    (a3 : Relation.ReflTransGen (FinalCount.H.HStep2C C L γ η w κ) h₂ h₃) (h0 : InvL M₀ R L γ η w κ h₀) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h₃ := by
  let P : HSt V D₀ → Prop := fun h => ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → ∀ R', InvL M₀ R' L γ η w κ a →
      ∃ R'', R'' ≤ R' ∧ InvL M₀ R'' L γ η w κ b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → P a → P b := by
    intro S hS a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih =>
      obtain ⟨R', hR', hI⟩ := ih
      obtain ⟨R'', hR'', hI''⟩ := hS _ _ hs R' hI
      exact ⟨R'', hR''.trans hR', hI''⟩
  exact key (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) a3
    (key (fun a b hs R' hI => hI.stepD3'L hs) a2
    (key (fun a b hs R' hI => InvL.step1LE hs hI) a1 ⟨R, le_rfl, h0⟩))

/-- A hinge atom of `M_sub` is SG (main's `hinge_sgat`, G3RunN, from `HingeSG`). -/
theorem hinge_sgatE {C : FinalCount.H.CollData M₀} (hH : HingeSG C L γ η w κ) {v : V} (hv : v ∈ C.hinges) :
    SGat M₀ L γ η w κ v := by
  obtain ⟨f, s, -, -, ⟨hf, hs, hfs, hout⟩, hsg⟩ := hH v hv
  cases hof : M₀.out f
  · have hos : M₀.out s = true := by
      cases h : M₀.out s
      · exact absurd (hof.trans h.symm) hout
      · rfl
    exact ⟨f, s, hf, hs, hof, hos, hfs, hsg⟩
  · have hos : M₀.out s = false := by
      cases h : M₀.out s
      · rfl
      · exact absurd (hof.trans h.symm) hout
    refine ⟨s, f, hs, hf, hos, hof, ?_, ?_⟩
    · intro e; apply hfs; rw [e, M₀.mate_mate]
    · have hsw : Molecule.gapAt L w κ s f = -Molecule.gapAt L w κ f s := by
        unfold Molecule.gapAt; abel
      rw [hsw, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (Molecule.gapAt L w κ f s))]
      exact hsg

/-- **The auxiliary invariants and no eligible triangle at the end of the run** (main's `HRunL.final`, GL9). -/
theorem HRunLE.final {C : FinalCount.H.CollData M₀} {h₀ hf : HSt V D₀} (hr : HRunLE C L γ η w κ h₀ hf)
    (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hinit : h₀ = HSt.init M₀) :
    FinalCount.H.RunAux M₀ C hf ∧ FinalCount.H.NoEligibleTriangle C L γ η w κ hf := by
  subst hinit
  obtain ⟨h₁, h₂, h₃, h₄, a1, -, a2, -, a3, n3, a4, hsgl, a5, -⟩ := hr
  have i0 : InvL M₀ R L γ η w κ (HSt.init M₀) := InvL.init hS h0
  obtain ⟨R₃, hR₃, i3⟩ := HRunLE.inv3 a1 a2 a3 i0
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → FinalCount.H.RunAux M₀ C a → FinalCount.H.RunAux M₀ C b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → FinalCount.H.RunAux M₀ C a → FinalCount.H.RunAux M₀ C b :=
    fun hS a b hab ha => rtgH (P := fun h => FinalCount.H.RunAux M₀ C h) hS hab ha
  have p1 := key (fun a b hs hp => HStep1LE.aux hs hp) a1 (FinalCount.H.RunAux.init C)
  have p2 := key (fun a b hs hp => hs.aux hp) a2 p1
  have p3 := key (fun a b hs hp => hs.aux hp) a3 p2
  have p4 := key (fun a b hs hp => hs.aux hp) a4 p3
  have hN : FinalCount.H.NoEpsHinge C h₄ := fun v hv hε hvH => hsgl v hv hε (hinge_sgatE hH hvH)
  refine ⟨?_, ?_⟩
  · exact (rtgH (P := fun h => FinalCount.H.RunAux M₀ C h ∧ FinalCount.H.NoEpsHinge C h)
      (fun a b hs hp => ⟨⟨hs.dp hp.1.1 hp.1.2.1.inj, hs.anc hp.1.2.1, hp.1.2.2.step4 hs hp.1.2.1 hp.2⟩,
        hp.2.step4 hs⟩) a5 ⟨p4, hN⟩).1
  · have k4 := rtgH (P := fun h => (∃ R', InvL M₀ R' L γ η w κ h) ∧ FinalCount.H.NoEligibleTriangle C L γ η w κ h)
      (fun h h' hs hP => ⟨by obtain ⟨R', hR'⟩ := hP.1; exact ⟨R', hR'.step3 hs.toHStep3⟩,
        hP.2.step3 (by obtain ⟨R', hR'⟩ := hP.1; exact hR'.good.1.noloop) hs.toHStep3⟩) a4 ⟨⟨R₃, i3⟩, n3⟩
    exact (rtgH (P := fun h => (∃ R', InvL M₀ R' L γ η w κ h) ∧ FinalCount.H.NoEligibleTriangle C L γ η w κ h)
      (fun h h' hs hP => ⟨by obtain ⟨R', hR'⟩ := hP.1; exact ⟨R', hR'.step4 hs⟩,
        hP.2.step4 (by obtain ⟨R', hR'⟩ := hP.1; exact hR'.good.1.noloop) hs⟩) a5 k4).2

/-! ### `cycles` (GL10) -/

/-- The recorded pair of a non-`ε` atom is designated (main's `desig_pairL`, GL10, from `HingeSG`). -/
theorem desig_pairLE {C : FinalCount.H.CollData M₀} {hf : HSt V D₀} (hb : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2)
    (hH : HingeSG C L γ η w κ) (hA : AncRel M₀ hf.s hf.anc) (hg : Clean hf.s)
    (hrec : HInv L γ η w κ hf) (hdp : DPInv hf) (hdes : FinalCount.H.DesRecN C hf) {c : V} (hc : c ∈ hf.s.M.atoms)
    (hne : hf.s.cls c ≠ .eps) {x y : hf.s.D} (hx : hf.s.M.atom x = c) (hy : hf.s.M.atom y = c) (hxy : x ≠ y) :
    FinalCount.H.Desig C (hf.anc c) (hf.s.pr x y) := by
  obtain ⟨p, vis, hr⟩ : ∃ p vis, hf.crec c = some (p, vis) := by
    have ok := hrec.ok c hc
    rcases hcl : hf.s.cls c with _ | ⟨ρ, kp⟩ | _ | _
    · exact absurd hcl hne
    · obtain ⟨-, p, vis, hr, -⟩ := ok.1 ρ kp hcl
      exact ⟨p, vis, hr⟩
    · obtain ⟨p, vis, hr, -⟩ := ok.2 hcl
      exact ⟨p, vis, hr⟩
    · exact absurd hcl (hg c hc)
  have hAm : hf.anc c ∈ M₀.atoms := hA.mem c hc
  have hdx : hf.s.down x ∈ M₀.dartsAt (hf.anc c) := by
    rw [mem_dartsAt, hA.atom x, hx]
  have hdy : hf.s.down y ∈ M₀.dartsAt (hf.anc c) := by
    rw [mem_dartsAt, hA.atom y, hy]
  have hcard : (M₀.dartsAt (hf.anc c)).card ≤ 4 := deg_le_four M₀ (hb _ hAm)
  have hne' : hf.s.down x ≠ hf.s.down y := fun e => hxy (hA.inj e)
  refine FinalCount.H.desig_of_sub hcard ?_ (q := hf.s.pr x y) hdx hdy hne' ?_ (hdes c p vis hr)
  · intro hHc f' s' hf' hs'
    obtain ⟨f, s, hf0, hs0, ⟨hfa, hsa, hfs, hout⟩, -⟩ := hH _ hHc
    have e1 : f' = f := Option.some.inj (hf'.symm.trans hf0)
    have e2 : s' = s := Option.some.inj (hs'.symm.trans hs0)
    subst e1 e2
    exact ⟨(mem_dartsAt _ _ _).2 hfa, (mem_dartsAt _ _ _).2 hsa, fun e => hout (by rw [e])⟩
  · have hsub : ({(hf.s.pr x y).1, (hf.s.pr x y).2} : Set D₀) ⊆ DSet hf.s c := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
    rcases hdp.ok c hc p vis hr with he | hdis
    · left
      rw [he] at hsub
      have h1 : (hf.s.pr x y).1 ∈ ({p.1, p.2} : Set D₀) := hsub (by simp)
      have h2 : (hf.s.pr x y).2 ∈ ({p.1, p.2} : Set D₀) := hsub (by simp)
      have hne2 : (hf.s.pr x y).1 ≠ (hf.s.pr x y).2 := hne'
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 ⊢
      rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hne2
      · rw [e1, e2]
      · rw [e1, e2]; tauto
      · exact absurd (e1.trans e2.symm) hne2
    · right
      exact Set.disjoint_of_subset_left hsub hdis

/-- **`cycles` for the LOW run with re-cuts** (main's `HRunL.cycles`, GL10). -/
theorem HRunLE.cycles [Infinite V] {C : FinalCount.H.CollData M₀} {hf : HSt V D₀}
    (hr : HRunLE C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) → CycleShape hf.s a := by
  obtain ⟨R', hR', hI⟩ := HRunLE.inv hr (InvL.init hS h0)
  have hgR' := hI.good
  have hst : FinalStructL R hf.s := FinalStructL.of_good hR' hI.good hI.comp
  obtain ⟨⟨hdp, hA, hD⟩, hNE⟩ := HRunLE.final hr hS hH h0 rfl
  intro a ha hev hne
  refine cycles_of_key hst.ab_deg (fun c hc => (hst.deg_range c hc).1) hI.bal hI.noloop ?_ ha hev hne
  intro T ⟨ρ0, k0, h0'⟩ ⟨ρ1, k1, h1'⟩ hne2
  have hcl : ∀ j : Fin 3, hf.s.cls (T.t j) ≠ .eps → hf.s.cls (T.t j) ≠ .ghost := fun j hj =>
    fun e => hgR'.2 _ (T.t_mem j) e
  have hxy : ∀ j : Fin 3, T.a j ≠ T.b j := fun j e => by
    have := T.out_a j; have h2 := T.out_b j; rw [e] at this; rw [this] at h2; exact absurd h2 (by simp)
  have hne0 : hf.s.cls (T.t 0) ≠ .eps := by rw [h0']; simp
  have hne1 : hf.s.cls (T.t 1) ≠ .eps := by rw [h1']; simp
  refine hNE T ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hI.alpha_sg _ (T.t_mem 0) ρ0 k0 h0' _ _ (T.atom_a 0) (T.atom_b 0) (T.out_a 0) (T.out_b 0)
    · exact hI.alpha_sg _ (T.t_mem 1) ρ1 k1 h1' _ _ (T.atom_a 1) (T.atom_b 1) (T.out_a 1) (T.out_b 1)
  · exact hI.gap_ne (T.t_mem 2) hne2 (hcl 2 hne2) (T.atom_a 2) (T.atom_b 2) (T.out_a 2) (T.out_b 2)
  · intro j
    have hj : hf.s.cls (T.t j) ≠ .eps := by
      fin_cases j
      · exact hne0
      · exact hne1
      · exact hne2
    exact desig_pairLE hS.bounds hH hA hgR'.2 hI.hrec hdp hD (T.t_mem j) hj (T.atom_a j) (T.atom_b j) (hxy j)

end WaveTurbulence.GammaLow.Flower.H2
