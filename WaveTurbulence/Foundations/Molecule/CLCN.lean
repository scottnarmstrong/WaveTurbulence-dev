/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockGeometricDichotomy
public import WaveTurbulence.Foundations.Molecule.ChainCNPattern
public import WaveTurbulence.Foundations.Molecule.HyperCannotConcatenate
public import WaveTurbulence.Foundations.Molecule.ChainSplicedMolecule
public import WaveTurbulence.Foundations.Molecule.CNBlockBound
public import WaveTurbulence.Foundations.Molecule.CNBlockExcess
public import WaveTurbulence.Foundations.Molecule.RootBlockPacking
public import WaveTurbulence.Foundations.Molecule.CNParentPreservation
public import WaveTurbulence.Foundations.Molecule.GeneralizedTrees
public import WaveTurbulence.Foundations.Molecule.RootPairComponents

/-! # M3 CLCN: block geometry, actual splicing, chains and deletion bounds

TARGET `block_clcn` (L1345–1366), `blockchainprop` (L1379–1382), and
`cnblock` (L1367–1376), with the accepted connected-block convention F57.
All constructions use the accepted MOLE garden and molecule definitions.
This is a pre-freeze scratch entry point; no frozen or root file is changed.
-/

public section
