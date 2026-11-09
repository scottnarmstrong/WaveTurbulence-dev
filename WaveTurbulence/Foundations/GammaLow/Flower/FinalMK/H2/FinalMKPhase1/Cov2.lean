/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov2
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
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Book
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Book2
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Cov1
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
/-! **L8-H2 port of main `WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov2`** (sha256 in H2/COPIED-SHA256SUMS): only the declarations
that depend on the vine-family carrier, re-stated over L6's low run (`FinalCount.H`, `Src … Src.γL`,
`Step1.VineCut Src.γL`) and L8's marked carrier (`SurvivorDataG Src.γL`); everything else is main's,
by import. Low-range changes are marked `L8-H2:` at their site (H2-PLAN §0).

 # C1b1 MK-PHASE1 (13): cut data of a matched object (coverage, part 2)

`vineDataA`: main's `vineDataL_of_intact` (LowChain22) for an object present through a renaming `π` (`MatchA`): a vine
cut `K` of the state along the transported object with the fresh names `fresh3 h 0, 1`, node darts in `U`, joints
`π U.upper`, `π U.lower` (so `anc` of the joints are the joints of `U`), the joint pairs, the `SG` gap of the first pair
and the twin relation; every cut with these atoms is a single vine when `U` is one. Copied by source. -/
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
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Cut data of a matched object** (main's `vineDataL_of_intact` with the renaming `π`). -/
theorem vineDataA [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀)
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hmate : ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h : HSt V D₀) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hinj : ∀ c ∈ h.s.M.atoms, ∀ e ∈ h.s.M.atoms, h.anc c = h.anc e → c = e)
    (hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4) (U : Src.Object Src.γL M₀) {π : V → V} (hm : MatchA h U π)
    (hsg : U.HasGapKind L γ η w κ .SG) :
    ∃ K : Step1.VineCut Src.γL h.s.M, K.C.atoms = U.atoms.image π ∧ K.C.upper = π U.upper ∧ K.C.lower = π U.lower ∧
      K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
      (U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂)) ∧
      (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∧
      FinalCount.H.SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) ∧
      FinalCount.H.SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂) ∧
      (FinalCount.H.ObjVine M₀ U → ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Step1.SingleVineVCGamma K') := by
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
    intro x e
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  obtain ⟨hf0, hf1⟩ := fresh3_spec h
  have hfab : fresh3 h 0 ≠ fresh3 h 1 := fun e => by have := hf0 e; simp at this
  obtain ⟨Ũ, hatoms, hup, hlo, hcd, hsv⟩ := stateObjA_spec hA hD hinj hm
  obtain ⟨K, hKC, hKfa, hKfb⟩ := FinalCount.H.exists_vineCut_of_object Ũ hdeg hnl (fresh3 h 0) (fresh3 h 1) (hf1 0) (hf1 1) hfab
  have hUup : U.upper ∈ U.atoms := FinalCount.H.object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := FinalCount.H.object_mem_of_joint U (Or.inr rfl)
  have hKup : K.C.upper = π U.upper := by rw [hKC]; exact hup
  have hKlo : K.C.lower = π U.lower := by rw [hKC]; exact hlo
  have hCD : ∀ z, K.C.ContainsDart z ↔ U.ContainsDart (h.s.down z) := fun z => by rw [hKC]; exact hcd z
  have hMx₁ : M₀.atom (h.s.down K.x₁) = U.upper := by rw [hA.atom, K.Mx₁, hKup]; exact hm.anc _ hUup
  have hMx₂ : M₀.atom (h.s.down K.x₂) = U.upper := by rw [hA.atom, K.Mx₂, hKup]; exact hm.anc _ hUup
  have hMy₁ : M₀.atom (h.s.down K.y₁) = U.lower := by rw [hA.atom, K.My₁, hKlo]; exact hm.anc _ hUlo
  have hMy₂ : M₀.atom (h.s.down K.y₂) = U.lower := by rw [hA.atom, K.My₂, hKlo]; exact hm.anc _ hUlo
  have PU : FinalCount.H.SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) :=
    ⟨hMx₂, hMx₁, (hCD _).mp K.in_a.2, (hCD _).mp K.in_a.1, by rw [hD.out]; exact K.Mout₂, by rw [hD.out]; exact K.Mout₁⟩
  have PL : FinalCount.H.SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) :=
    ⟨hMy₂, hMy₁, (hCD _).mp K.in_b.2, (hCD _).mp K.in_b.1, by rw [hD.out]; exact K.Mouty₂,
      by rw [hD.out]; exact K.Mouty₁⟩
  refine ⟨K, by rw [hKC, hatoms], hKup, hKlo, hKfa, hKfb, ⟨(hCD _).mp K.in_a.1, (hCD _).mp K.in_a.2,
    (hCD _).mp K.in_b.1, (hCD _).mp K.in_b.2⟩, ⟨hMx₁, hMy₁⟩, PU, PL, ?_, ?_, ?_⟩
  · have := FinalCount.H.object_gapKind_pair U L γ η w κ .SG hsg PU
    rw [gapAt_comp_down]
    have e : Molecule.gapAt L w κ (h.s.down K.x₁) (h.s.down K.x₂) =
        -Molecule.gapAt L w κ (h.s.down K.x₂) (h.s.down K.x₁) := by
      simp [Molecule.gapAt]
    rw [e, gapKind_neg]; exact this
  · have htw := FinalCount.H.object_gap_twin U (fun b hb => Mole.deg_le_four M₀ hM₀ hb) (Molecule.kvec L w κ)
      (fun x => by simp [Molecule.kvec, hmate]) h0 PU PL
    unfold pgap
    simp only [St.pr, Molecule.gapAt]
    rw [eq_neg_iff_add_eq_zero]
    calc _ = -((Molecule.kvec L w κ (h.s.down K.x₂) - Molecule.kvec L w κ (h.s.down K.x₁)) +
          (Molecule.kvec L w κ (h.s.down K.y₂) - Molecule.kvec L w κ (h.s.down K.y₁))) := by abel
      _ = 0 := by rw [htw, neg_zero]
  · intro hov K' hK'
    exact hsv K' (hK'.trans (by rw [hKC, hatoms])) hov

end WaveTurbulence.GammaLow.Flower.H2
