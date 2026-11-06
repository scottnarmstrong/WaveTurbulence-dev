/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Bump
public import WaveTurbulence.Foundations.ClassJR.Chain
public import WaveTurbulence.Foundations.ClassJR.Chain2
public import WaveTurbulence.Foundations.ClassJR.ChainPartition
public import WaveTurbulence.Foundations.ClassJR.ClassDef
public import WaveTurbulence.Foundations.ClassJR.CompJJ
public import WaveTurbulence.Foundations.ClassJR.CompJJSetup
public import WaveTurbulence.Foundations.ClassJR.CompJR
public import WaveTurbulence.Foundations.ClassJR.CompJR2
public import WaveTurbulence.Foundations.ClassJR.CompKernel
public import WaveTurbulence.Foundations.ClassJR.CompRJ
public import WaveTurbulence.Foundations.ClassJR.CompRR
public import WaveTurbulence.Foundations.ClassJR.CompRR2
public import WaveTurbulence.Foundations.ClassJR.Convert
public import WaveTurbulence.Foundations.ClassJR.Coupling
public import WaveTurbulence.Foundations.ClassJR.CouplingRR
public import WaveTurbulence.Foundations.ClassJR.CouplingS
public import WaveTurbulence.Foundations.ClassJR.IJI
public import WaveTurbulence.Foundations.ClassJR.IJI2
public import WaveTurbulence.Foundations.ClassJR.IJI3
public import WaveTurbulence.Foundations.ClassJR.IJI4
public import WaveTurbulence.Foundations.ClassJR.IJI5
public import WaveTurbulence.Foundations.ClassJR.IJI6
public import WaveTurbulence.Foundations.ClassJR.IJI7
public import WaveTurbulence.Foundations.ClassJR.IJI8
public import WaveTurbulence.Foundations.ClassJR.IJI9
public import WaveTurbulence.Foundations.ClassJR.IRI
public import WaveTurbulence.Foundations.ClassJR.IRI2
public import WaveTurbulence.Foundations.ClassJR.IRI3
public import WaveTurbulence.Foundations.ClassJR.IRI4
public import WaveTurbulence.Foundations.ClassJR.IRI5
public import WaveTurbulence.Foundations.ClassJR.IRI6
public import WaveTurbulence.Foundations.ClassJR.IRI7
public import WaveTurbulence.Foundations.ClassJR.IRI8
public import WaveTurbulence.Foundations.ClassJR.InvBounds
public import WaveTurbulence.Foundations.ClassJR.JRChain
public import WaveTurbulence.Foundations.ClassJR.Kernel
public import WaveTurbulence.Foundations.ClassJR.KernelM
public import WaveTurbulence.Foundations.ClassJR.LegalPartitions
public import WaveTurbulence.Foundations.ClassJR.Lemma53
public import WaveTurbulence.Foundations.ClassJR.Lemma54a
public import WaveTurbulence.Foundations.ClassJR.Lemma54b
public import WaveTurbulence.Foundations.ClassJR.Lemma55
public import WaveTurbulence.Foundations.ClassJR.Lemma56
public import WaveTurbulence.Foundations.ClassJR.Lemma57
public import WaveTurbulence.Foundations.ClassJR.Lemma58
public import WaveTurbulence.Foundations.ClassJR.MCAssemble
public import WaveTurbulence.Foundations.ClassJR.MCCase1
public import WaveTurbulence.Foundations.ClassJR.MCChain1
public import WaveTurbulence.Foundations.ClassJR.MCChainExp
public import WaveTurbulence.Foundations.ClassJR.MCChainF
public import WaveTurbulence.Foundations.ClassJR.MCChainId
public import WaveTurbulence.Foundations.ClassJR.MCChainM
public import WaveTurbulence.Foundations.ClassJR.MCChainOne
public import WaveTurbulence.Foundations.ClassJR.MCChainT
public import WaveTurbulence.Foundations.ClassJR.MCChainTerm
public import WaveTurbulence.Foundations.ClassJR.MCChainX
public import WaveTurbulence.Foundations.ClassJR.MCCodes
public import WaveTurbulence.Foundations.ClassJR.MCCodesVars
public import WaveTurbulence.Foundations.ClassJR.MCConst
public import WaveTurbulence.Foundations.ClassJR.MCDefs
public import WaveTurbulence.Foundations.ClassJR.MCDiff
public import WaveTurbulence.Foundations.ClassJR.MCE
public import WaveTurbulence.Foundations.ClassJR.MCG
public import WaveTurbulence.Foundations.ClassJR.MCGP
public import WaveTurbulence.Foundations.ClassJR.MCGR
public import WaveTurbulence.Foundations.ClassJR.MCK1
public import WaveTurbulence.Foundations.ClassJR.MCMain
public import WaveTurbulence.Foundations.ClassJR.MCOne
public import WaveTurbulence.Foundations.ClassJR.MCPair
public import WaveTurbulence.Foundations.ClassJR.MCProd
public import WaveTurbulence.Foundations.ClassJR.MCProp51
public import WaveTurbulence.Foundations.ClassJR.MCProp51T
public import WaveTurbulence.Foundations.ClassJR.MCReorder
public import WaveTurbulence.Foundations.ClassJR.MCSRep
public import WaveTurbulence.Foundations.ClassJR.MCSob
public import WaveTurbulence.Foundations.ClassJR.MCSum
public import WaveTurbulence.Foundations.ClassJR.MCTBound
public import WaveTurbulence.Foundations.ClassJR.MCTExp
public import WaveTurbulence.Foundations.ClassJR.MCTMain
public import WaveTurbulence.Foundations.ClassJR.MCTOne
public import WaveTurbulence.Foundations.ClassJR.MCTShift
public import WaveTurbulence.Foundations.ClassJR.MCTTerm
public import WaveTurbulence.Foundations.ClassJR.MCType1
public import WaveTurbulence.Foundations.ClassJR.MCType2
public import WaveTurbulence.Foundations.ClassJR.Masked
public import WaveTurbulence.Foundations.ClassJR.Masked2
public import WaveTurbulence.Foundations.ClassJR.OfAny
public import WaveTurbulence.Foundations.ClassJR.Param
public import WaveTurbulence.Foundations.ClassJR.ParamComp
public import WaveTurbulence.Foundations.ClassJR.ParamDeriv
public import WaveTurbulence.Foundations.ClassJR.ParamJR
public import WaveTurbulence.Foundations.ClassJR.ParamJR2
public import WaveTurbulence.Foundations.ClassJR.Reindex
public import WaveTurbulence.Foundations.ClassJR.Symbol
public import WaveTurbulence.Foundations.ClassJR.Triple
public import WaveTurbulence.Foundations.ClassJR.TripleS

/-! Public re-exports for FoundationsClassJR.
Generated by scripts/update_root_imports.py. -/
public section
