/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Run2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChain2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmConn1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmConn2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmRun2
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Bal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Elig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Ex1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Ex1New
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Final2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalE3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalE4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Prop95
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Range
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineBall
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineObj3
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL29
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GM08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV05
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV06
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV09
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.HyperAtomClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain16
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain17
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain18
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain19
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain29
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenClass
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenCn3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopFacts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopMain3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenOne
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenSplit3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGlue
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.Prop95Core
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceCL
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceCN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceGroup
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVCTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVCTop2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceIngr
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceMarked
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceObj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceObj3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceRev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceRuns
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSkip
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSpine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceStage
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSurvData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceUnitBlocks
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceUnits
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceUnits2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceV0
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Collection
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Erase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Exists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Gaps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Overlap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1OverlapMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Split
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Unique
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Vinechain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SourceVinePartitionInput
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Disj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproChainSplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproCollDisj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproGap2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproInterleaved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproOneJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeC1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeConn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeRem
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeStraddle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproStep1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproSupportA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.VrHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapAdjointClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapShortAdjoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVBlockBranchEquality
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVDegrees
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMixedRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryShapes
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVTypeIRemoval
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLargeVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineOrdinarySplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGMixedRemovalVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGNonVII
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalSingle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryRemovalVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGOrdinaryVineShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSplitJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInHyperLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSideVIILength
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCVineLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverAdmissible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverBudget
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverFineBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverTags
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.EvalAssemble
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.EvalGate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.FinalCountMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularAssembly
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularCoupleP
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularGardenP
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularPrefix
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceAtomScaleExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDef
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingCardLimits
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingChoiceScales
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceFinalCountInputs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceFullPairTable
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamond
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceLadderGapExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePairsMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePrimaryPairChoices
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePrimaryPairTable
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceRestrictedCarrier
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSecondCollectionExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpineInputsS10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedChoiceScaleAbsorption
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedCircuitRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredCountA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredGates
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredRawBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFiniteSupport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedKernelFormula
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSelectedAbsoluteSum
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSelectedKernel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSourceInterpolation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSumIntegral
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1CoreBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1GateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1PieceBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1SumBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1TypeBound
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
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.Run1
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKStep.State
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Bank
/-! **L8-H2 port of main `WaveTurbulence.Foundations.Flower.FinalMKStep.Run2`** (sha256 in H2/COPIED-SHA256SUMS): only the declarations
that depend on the vine-family carrier, re-stated over L6's low run (`FinalCount.H`, `Src … Src.γL`,
`Step1.VineCut Src.γL`) and L8's marked carrier (`SurvivorDataG Src.γL`); everything else is main's,
by import. Low-range changes are marked `L8-H2:` at their site (H2-PLAN §0).

 # C1a SURV-STEP (6): the LOW run with re-cuts, part 2 (`HRunLE.noTriple`, `HRunLE.prop95L`)

Copy-thread of main's GL11 `noTripleBond_of_stopL` and GL12 `HRunL.noTriple`/`HRunL.prop95L` (sha256 in
COPIED-SHA256SUMS) to `HRunLE`: Step-1 inductions run over `HStep1LE` (`HStep1LE.aux`, `HStep1LE.epsLe`, `HRunLE.inv1`),
and `SubproOblG` is replaced by its field `HingeSG`. The conclusion is main's `Prop95ConclL` unchanged, so the final-state
lemmas of G3-LOWDEG (GV01–GV13, `Prop95ConclL.toAtL`) apply to the run with re-cuts as they are. -/
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

/-- No triple bond after Step 1 with re-cuts (main's `noTripleBond_of_stopL`, GL11, R37(b)). -/
theorem noTripleBond_of_stopLE [Infinite V] {C : FinalCount.H.CollData M₀} {h₁ : HSt V D₀} (hS : SubHypL R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hHg : HingeSG C L γ η w κ) (hT : FinalCount.H.TripleDesig C)
    (a1 : Relation.ReflTransGen (HStep1LE C L γ η w κ) (HSt.init M₀) h₁) (n1 : FinalCount.H.NoTripleCut C L γ η w κ h₁) :
    NoTripleBond h₁.s.M := by
  obtain ⟨R', hR', i1⟩ := HRunLE.inv1 a1 (InvL.init hS h0)
  have hA : AncRel M₀ h₁.s h₁.anc :=
    (rtgH (P := fun h => FinalCount.H.RunAux M₀ C h) (fun _ _ hs hr => HStep1LE.aux hs hr) a1 (FinalCount.H.RunAux.init C)).2.1
  have e : EpsLe (HSt.init M₀).s h₁.s :=
    rtgH (P := fun h => EpsLe (HSt.init M₀).s h.s) (fun _ _ hs he => he.trans (HStep1LE.epsLe hs)) a1 (EpsLe.refl _)
  have hg := i1.good
  have hD := i1.rel
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hbs : h₁.s.M.bondsBetween b a = h₁.s.M.bondsBetween a b := by
    unfold Molecule.bondsBetween; simp only [Sym2.eq_swap]
  have hda : 3 ≤ h₁.s.M.deg a := hcon.trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ h₁.s.M.deg b := by rw [← hbs] at hcon; exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : h₁.s.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : h₁.s.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a0, -⟩, ⟨b0, -⟩, hle⟩ := e a ha b hb hea heb
  obtain ⟨v, c, x, y, hvc, hH, hf, hs, hTA, hmx, hmy⟩ := hT a b a0 b0 hab (hcon.trans hle)
  -- the hinge endpoint `v` and the other endpoint `c`, as atoms of `h₁`
  have key : ∀ v c : V, v ∈ h₁.s.M.atoms → c ∈ h₁.s.M.atoms → h₁.s.cls v = .eps → h₁.s.cls c = .eps → v ≠ c →
      3 ≤ h₁.s.M.bondsBetween v c → 3 ≤ h₁.s.M.deg v → v ∈ C.hinges → ∀ x y, C.first v = some x →
      C.second v = some y → TripleAtM M₀ v x y → M₀.atom (M₀.mate x) = c → M₀.atom (M₀.mate y) = c → False := by
    intro v c hv hc hεv hεc hvc' hb3 hdv hHv x y hf hs hTA hmx hmy
    obtain ⟨hxa, hya, hyx, hxy⟩ := hTA
    obtain ⟨X, hXd, hXa, hXm⟩ := eps_dart_lift hA hD hv hεv hc hεc hxa hmx
    obtain ⟨Y, hYd, hYa, hYm⟩ := eps_dart_lift hA hD hv hεv hc hεc hya hmy
    have hoX : h₁.s.M.out X = M₀.out x := by rw [← hD.out, hXd]
    have hoY : h₁.s.M.out Y = M₀.out y := by rw [← hD.out, hYd]
    have hanc : h₁.anc v = v := hA.eps v hv hεv
    obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset h₁.s.M.atoms
    obtain ⟨x₀, y₀, hx₀, hy₀, -, hsgxy⟩ := hHg v hHv
    have ex : x₀ = x := Option.some.inj (hx₀.symm.trans hf)
    have ey : y₀ = y := Option.some.inj (hy₀.symm.trans hs)
    rw [ex, ey] at hsgxy
    have hdesxy : FinalCount.H.Desig C v (x, y) := fun _ => ⟨x, y, hf, hs, Or.inl (by simp)⟩
    have hdesyx : FinalCount.H.Desig C v (y, x) := fun _ => ⟨x, y, hf, hs, Or.inl (by simp [Set.pair_comm])⟩
    have hneX : Y ≠ h₁.s.M.mate X := by
      intro hh; apply hyx
      have := congrArg h₁.s.down hh
      rw [hYd, ← hD.mate, hXd] at this; exact this
    have hneY : X ≠ h₁.s.M.mate Y := by
      intro hh; apply hyx
      have := congrArg h₁.s.down hh
      rw [hXd, ← hD.mate, hYd] at this
      rw [this, M₀.mate_mate]
    cases hox : M₀.out x
    · -- x incoming: (X, Y)
      have hoy : M₀.out y = true := by
        cases h' : M₀.out y
        · exact absurd (hox.trans h'.symm) hxy
        · rfl
      have hc' : h₁.s.M.IsCutData v v₂ X Y := ⟨hv, hv₂, hXa, hYa, hneX, by rw [hoX, hox], by rw [hoY, hoy]⟩
      refine n1 v v₂ X Y hc' hεv hdv (by rw [hanc]; exact hHv) (by rw [hanc]; simpa [St.pr, hXd, hYd] using hdesxy) ⟨c, hvc'.symm, hb3, hXm, hYm⟩ ?_
      show Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h₁.s.down) X Y) = .SG
      have : Molecule.gapAt L w (κ ∘ h₁.s.down) X Y = Molecule.gapAt L w κ x y := by
        unfold Molecule.gapAt Molecule.kvec; simp [Function.comp, hXd, hYd]
      rw [this]; exact hsgxy
    · -- x outgoing: (Y, X)
      have hoy : M₀.out y = false := by
        cases h' : M₀.out y
        · rfl
        · exact absurd (hox.trans h'.symm) hxy
      have hc' : h₁.s.M.IsCutData v v₂ Y X := ⟨hv, hv₂, hYa, hXa, hneY, by rw [hoY, hoy], by rw [hoX, hox]⟩
      refine n1 v v₂ Y X hc' hεv hdv (by rw [hanc]; exact hHv) (by rw [hanc]; simpa [St.pr, hXd, hYd] using hdesyx) ⟨c, hvc'.symm, hb3, hYm, hXm⟩ ?_
      show Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h₁.s.down) Y X) = .SG
      have : Molecule.gapAt L w (κ ∘ h₁.s.down) Y X = -Molecule.gapAt L w κ x y := by
        unfold Molecule.gapAt Molecule.kvec; simp [Function.comp, hXd, hYd]
      rw [this, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg _)]; exact hsgxy
  rcases hvc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key v c ha hb hea heb hab hcon hda hH x y hf hs hTA hmx hmy
  · exact key v c hb ha heb hea hab.symm (by rw [hbs]; exact hcon) hdb hH x y hf hs hTA hmx hmy

/-- No triple bonds at the end of the LOW run with re-cuts (main's `HRunL.noTriple`, GL12). -/
theorem HRunLE.noTriple [Infinite V] {C : FinalCount.H.CollData M₀} {hf : HSt V D₀} (hr : HRunLE C L γ η w κ (HSt.init M₀) hf)
    (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ) (hT3 : FinalCount.H.TripleDesig C)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {R' : ℕ} (hg : Good R' hf.s) : NoTripleBond hf.s.M := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1c, a2, -, a3, -, a4, -, a5, -⟩ := hr
  have n1 : NoTripleBond h₁.s.M := noTripleBond_of_stopLE hS h0 hH hT3 a1 n1c
  have e2 : EpsLe h₁.s h₂.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans (by
      obtain ⟨v, x₁, x₂, hD, rfl⟩ := hs.data
      exact EpsLe.betaSt v)) a2 (EpsLe.refl _)
  have e3 : EpsLe h₁.s h₃.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep2.step.epsLe) a3 e2
  have e4 : EpsLe h₁.s h₄.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep3.step.epsLe) a4 e3
  have e : EpsLe h₁.s hf.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.step.epsLe) a5 e4
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hda : 3 ≤ hf.s.M.deg a := (hcon.trans' (le_refl _)).trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ hf.s.M.deg b := by
    have : hf.s.M.bondsBetween a b = hf.s.M.bondsBetween b a := by
      unfold Molecule.bondsBetween
      simp only [Sym2.eq_swap]
    rw [this] at hcon
    exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : hf.s.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : hf.s.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a1, -⟩, ⟨b1, -⟩, hle⟩ := e a ha b hb hea heb
  exact absurd (hcon.trans hle) (by have := n1 a a1 b b1 hab; omega)

/-- **DH23 Prop 9.5 / TARGET `finalmol` for the LOW run with re-cuts** (main's `HRunL.prop95L`, GL12). -/
theorem HRunLE.prop95L [Infinite V] {C : FinalCount.H.CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunLE C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ)
    (hT3 : FinalCount.H.TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclL L γ η w κ Tm R hf := by
  obtain ⟨R', hR', hI⟩ := HRunLE.inv hr (InvL.init hS h0)
  have hgR' := hI.good
  have hst : FinalStructL R hf.s := FinalStructL.of_good hR' hgR' hI.comp
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, hsgl, a5, n5⟩ := id hr
  have heps : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → Tm a ∨ ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG := by
    intro a ha hae
    by_cases hT : Tm a
    · exact Or.inl hT
    right
    intro x y hx hy hox hoy hxy
    have hrel := hI.rel
    obtain ⟨ha3, hae3⟩ := FinalCount.H.HRunN.eps_back a5 a ha hae
    have hnsg : ¬ SGat M₀ L γ η w κ a := hsgl a ha3 hae3
    have hx0 : M₀.atom (hf.s.down x) = a := by rw [hrel.eps x (by rw [hx]; exact hae), hx]
    have hy0 : M₀.atom (hf.s.down y) = a := by rw [hrel.eps y (by rw [hy]; exact hae), hy]
    have hox0 : M₀.out (hf.s.down x) = false := by rw [hrel.out]; exact hox
    have hoy0 : M₀.out (hf.s.down y) = true := by rw [hrel.out]; exact hoy
    have hxy0 : hf.s.down y ≠ M₀.mate (hf.s.down x) := by
      intro e
      have := hS.noloop (hf.s.down x)
      rw [← e, hx0, hy0] at this
      exact this rfl
    have haM : a ∈ M₀.atoms := hx0 ▸ M₀.atom_mem _
    have hgap : Molecule.gapAt L w (κ ∘ hf.s.down) x y = Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y) := rfl
    rw [hgap]
    by_contra hne
    have hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) = .SG ∨
        Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) = .ZG := by
      rcases hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) with _ | _ | _
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd hk hne
    rcases hk with hk | hk
    · exact hnsg ⟨hf.s.down x, hf.s.down y, hx0, hy0, hox0, hoy0, hxy0, hk⟩
    · rcases hdeg a haM _ _ hx0 hy0 hox0 hoy0 hxy0 hk with hsg | hTm
      · exact hnsg hsg
      · exact hT hTm
  exact
  { struct := hst
    label := by
      intro a ha ρ kp hc
      obtain ⟨hl, p, vis, hrec, hp, hkp, -, -⟩ := (hI.hrec.ok a ha).1 ρ kp hc
      refine ⟨hl, hkp, fun x y hx hy hox hoy _ => ?_⟩
      obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg a ha (by rw [hc]; simp) x y hx hy hox hoy
      rw [hrec] at hrec'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
      obtain ⟨rfl, rfl⟩ := hrec'
      unfold GapSim
      rw [norm_gap_of_pm hn]
      exact hp
    eps_LG := heps
    no_triple := HRunLE.noTriple hr hS hH hT3 h0 hgR'
    cycles := HRunLE.cycles hr hS hH h0
    chains := by
      intro a ha hev hne hex hT
      refine chainEnds_of hst.ab_deg (fun c hc => (hst.deg_range c hc).1) hI.bal ha
        (fun e he hce hae v₂ x₁ x₂ hcd => ?_) hev hne hex
      have hhT := hT e (Finset.mem_filter.2 ⟨he, hae⟩) hce
      exact n5 e he hhT.2 v₂ x₁ x₂ hcd
        (gapAt_ne_zero_of_LG ((heps e he hce).resolve_left hhT.1
          x₁ x₂ hcd.2.2.1 hcd.2.2.2.1 hcd.2.2.2.2.2.1 hcd.2.2.2.2.2.2 hcd.2.2.2.2.1))
    bal := hI.bal
    noloop := hI.noloop
    alpha_sg := by
      intro b hb ρ kp hc x y hx hy hox hoy
      obtain ⟨-, p, vis, hrec, -, -, -, hsg⟩ := (hI.hrec.ok b hb).1 ρ kp hc
      obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg b hb (by rw [hc]; simp) x y hx hy hox hoy
      rw [hrec] at hrec'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
      obtain ⟨rfl, rfl⟩ := hrec'
      rw [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_gap_of_pm hn)]
      exact hsg
    dartGap := by
      intro a ha hne x y hx hy hox hoy
      obtain ⟨p, vis, hrec, hn⟩ := hI.gap.dg a ha hne x y hx hy hox hoy
      exact ⟨pgap L w κ p, ⟨p, vis, hrec, rfl⟩, hn⟩
    noBetaCut := n5
    N1 := fun b hb hcb => hI.hrec.N1 hb hcb
    N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum =>
      hI.hrec.N2 hL hη h1 h2 hb c1 c2 cb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum }

/-- **The run facts of the LOW run with re-cuts** (the inputs of G3-LOWDEG's final-state lemmas, e.g. `no_SGL`): the
invariants at some index `≤ R`, the auxiliary invariants, no eligible triangle, and `Prop95ConclL`. -/
theorem HRunLE.runFacts [Infinite V] {C : FinalCount.H.CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunLE C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ)
    (hT3 : FinalCount.H.TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    (∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ hf) ∧ FinalCount.H.RunAux M₀ C hf ∧ FinalCount.H.NoEligibleTriangle C L γ η w κ hf ∧
      Prop95ConclL L γ η w κ Tm R hf :=
  ⟨HRunLE.inv hr (InvL.init hS h0), (HRunLE.final hr hS hH h0 rfl).1, (HRunLE.final hr hS hH h0 rfl).2,
    HRunLE.prop95L hr hS hH hT3 hdeg h0⟩

/-- `HRunLE` from a run without re-cuts and the `SubproOblG` of main (bridge: main's facts are recovered). -/
theorem HRunL.prop95L_viaE [Infinite V] {C : FinalCount.H.CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : FinalCount.H.HRunL C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (obl : FinalCount.H.SubproOblG C L γ η w κ)
    (hT3 : FinalCount.H.TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclL L γ η w κ Tm R hf :=
  HRunLE.prop95L (HRunL.toE hr) hS (SubproOblG.hingeSGP obl) hT3 hdeg h0

end WaveTurbulence.GammaLow.Flower.H2
