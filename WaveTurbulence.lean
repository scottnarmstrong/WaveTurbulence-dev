/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Imports.FoundationsAnalysis
public import WaveTurbulence.Imports.FoundationsApproxNT
public import WaveTurbulence.Imports.FoundationsCancel
public import WaveTurbulence.Imports.FoundationsCanon
public import WaveTurbulence.Imports.FoundationsClassJR
public import WaveTurbulence.Imports.FoundationsCombinatorics
public import WaveTurbulence.Imports.FoundationsCountLemmas
public import WaveTurbulence.Imports.FoundationsCounting
public import WaveTurbulence.Imports.FoundationsCumulant
public import WaveTurbulence.Imports.FoundationsFourier
public import WaveTurbulence.Imports.FoundationsGaussian
public import WaveTurbulence.Imports.FoundationsIncoh
public import WaveTurbulence.Imports.FoundationsIncohInst
public import WaveTurbulence.Imports.FoundationsLayered
public import WaveTurbulence.Imports.FoundationsLemLin
public import WaveTurbulence.Imports.FoundationsLinAlg
public import WaveTurbulence.Imports.FoundationsLinks
public import WaveTurbulence.Imports.FoundationsMainGlue
public import WaveTurbulence.Imports.FoundationsMolecule
public import WaveTurbulence.Imports.FoundationsNLS
public import WaveTurbulence.Imports.FoundationsNTSP
public import WaveTurbulence.Imports.FoundationsNumberTheory
public import WaveTurbulence.Imports.FoundationsProbability
public import WaveTurbulence.Imports.FoundationsRegAsymp
public import WaveTurbulence.Imports.FoundationsRegStruct
public import WaveTurbulence.Imports.FoundationsRegref
public import WaveTurbulence.Imports.FoundationsRegularAsymptotics
public import WaveTurbulence.Imports.FoundationsResonant
public import WaveTurbulence.Imports.FoundationsSpine
public import WaveTurbulence.Imports.FoundationsSumint
public import WaveTurbulence.Imports.FoundationsTorus
public import WaveTurbulence.Imports.FoundationsVdCB
public import WaveTurbulence.Imports.FoundationsVine
public import WaveTurbulence.Imports.FoundationsWKE
public import WaveTurbulence.Imports.FoundationsWKEL2
public import WaveTurbulence.Imports.FoundationsWaveB
public import WaveTurbulence.Imports.FoundationsWeylSums
public import WaveTurbulence.Imports.FoundationsXChain
public import WaveTurbulence.Imports.FrozenDefinitions
public import WaveTurbulence.Imports.FrozenTheorems

/-!
# WaveTurbulence

Root of the Lean formalization of Y. Deng and Z. Hani, *Long time justification of wave
turbulence theory*, arXiv:2311.10082v2.
-/

public section
