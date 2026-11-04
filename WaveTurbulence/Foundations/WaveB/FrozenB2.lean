/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.ChosenSet
public import WaveTurbulence.Frozen.Defs.GardenMatchesCouple
public import WaveTurbulence.Frozen.Defs.GardenMatchesPairedTree
public import WaveTurbulence.Frozen.Defs.GardenMatchesTreeCouple
public import WaveTurbulence.Frozen.Defs.InputRemainder
public import WaveTurbulence.Frozen.Defs.InstDecidableIsSpecialSet
public import WaveTurbulence.Frozen.Defs.IsRegularCouple
public import WaveTurbulence.Frozen.Defs.IsRegularTree
public import WaveTurbulence.Frozen.Defs.IsSpecialSet
public import WaveTurbulence.Frozen.Defs.LayeredGardenIncoherency
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniCplCodePartner
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeGreen
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeRed
public import WaveTurbulence.Frozen.Defs.Node3
public import WaveTurbulence.Frozen.Defs.PvResonantIntegral
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawCplMapTree
public import WaveTurbulence.Frozen.Defs.RawCplOpA
public import WaveTurbulence.Frozen.Defs.RawCplOpB
public import WaveTurbulence.Frozen.Defs.RawCplOrient
public import WaveTurbulence.Frozen.Defs.RawCplRelocate
public import WaveTurbulence.Frozen.Defs.RawCplTree
public import WaveTurbulence.Frozen.Defs.RawRegular
public import WaveTurbulence.Frozen.Defs.RegBound
public import WaveTurbulence.Frozen.Defs.RegChainApp
public import WaveTurbulence.Frozen.Defs.RegChainDecodesTree
public import WaveTurbulence.Frozen.Defs.RegChainIsNil
public import WaveTurbulence.Frozen.Defs.RegChainJBtree
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegChainTreeLinks
public import WaveTurbulence.Frozen.Defs.RegCplApp
public import WaveTurbulence.Frozen.Defs.RegCplDecodes
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
public import WaveTurbulence.Frozen.Defs.RegCplIsType2
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplLinks
public import WaveTurbulence.Frozen.Defs.RegCplLinksAtRegChainLinksAt
public import WaveTurbulence.Frozen.Defs.RegCplLinksAtRegChainLinksAt
public import WaveTurbulence.Frozen.Defs.RegCplMstarRegChainNstar
public import WaveTurbulence.Frozen.Defs.RegCplMstarRegChainNstar
public import WaveTurbulence.Frozen.Defs.RegCplPairsAtRegChainPairsAt
public import WaveTurbulence.Frozen.Defs.RegCplPairsAtRegChainPairsAt
public import WaveTurbulence.Frozen.Defs.RegCplRaw
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplTreesRegChainPlug
public import WaveTurbulence.Frozen.Defs.RegCplTreesRegChainPlug
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.ResIntegral
public import WaveTurbulence.Frozen.Defs.ResSlice
public import WaveTurbulence.Frozen.Defs.SlotSign
public import WaveTurbulence.Frozen.Defs.SpecialSets
public import WaveTurbulence.Frozen.Defs.SpecialWeight
public import WaveTurbulence.Frozen.Defs.SymmPairs
public import WaveTurbulence.Frozen.Defs.TTreeSetAt
public import WaveTurbulence.Frozen.Defs.TTreeSubtreeAt
public import WaveTurbulence.Frozen.Defs.TimeBox
public import WaveTurbulence.Frozen.Defs.TimeBoxGt
public import WaveTurbulence.Frozen.Defs.TreeOfSign
public import WaveTurbulence.Frozen.Defs.ZetaOfTrees

/-!
# The Wave B tier-B2 frozen definitions as one import

A non-frozen aggregator for the ported REG-STRUCT and INCOH-INST proofs, which were written against the
whole B2 Regular draft (`WaveB2Draft.RegularDefs`, `WaveB2Draft.Regular`). It imports the B1 aggregator
and every B2 definition anchor of `WaveTurbulence/Frozen/Defs/` (ruling D8); it declares nothing.
-/
