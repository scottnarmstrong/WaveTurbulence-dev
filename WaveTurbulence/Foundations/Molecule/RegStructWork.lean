/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CatalanGeneration
public import WaveTurbulence.Foundations.RegStruct.CodeCount
public import WaveTurbulence.Foundations.Molecule.ChainCount
public import WaveTurbulence.Foundations.RegStruct.CrossingSupport
public import WaveTurbulence.Foundations.RegStruct.CarrierUniqueness
public import WaveTurbulence.Foundations.Molecule.RawRepresentationBRoots
public import WaveTurbulence.Foundations.RegStruct.InsertionOutside
public import WaveTurbulence.Foundations.RegStruct.ChainPairLocations
public import WaveTurbulence.Foundations.RegStruct.NodeSeparation
public import WaveTurbulence.Foundations.RegStruct.SourceTreeCount
public import WaveTurbulence.Foundations.RegStruct.CodeUniqueness
public import WaveTurbulence.Foundations.RegStruct.SaturatedChainShape
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs
public import WaveTurbulence.Foundations.Molecule.DominantChains
public import WaveTurbulence.Foundations.Molecule.BareChainPairGeometry

/-! # Verified REG-STRUCT development interface

Source regularity is exactly the decoding range for couples and trees; all structure
data are unique. Legal partitions, dominant chains, actual restricted B-histories,
and fixed-sign exponential counts are proved against the pinned definitions.
-/

public section
