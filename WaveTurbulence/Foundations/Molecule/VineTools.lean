/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineObjects
public import WaveTurbulence.Foundations.Molecule.VineCoherenceExpansion
public import WaveTurbulence.Foundations.Molecule.VineSizeFormulas
public import WaveTurbulence.Foundations.Molecule.LadderCounts
public import WaveTurbulence.Foundations.Molecule.VineRealizationCounts
public import WaveTurbulence.Foundations.Molecule.VineRealizationPaths
public import WaveTurbulence.Foundations.Molecule.VineSigmaExpansion
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.Molecule.VineActualGroupSizes
public import WaveTurbulence.Foundations.Molecule.VineTripleGroup
public import WaveTurbulence.Foundations.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.Molecule.VineSubsetBarrier
public import WaveTurbulence.Foundations.Molecule.VineCoreClassification
public import WaveTurbulence.Foundations.Molecule.VineMaskedDegrees
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
public import WaveTurbulence.Foundations.Molecule.VineRungConstant
public import WaveTurbulence.Foundations.Molecule.VineBlockBalance
public import WaveTurbulence.Foundations.Molecule.VineRungPorts
public import WaveTurbulence.Foundations.Molecule.VineBaseSGSubsets
public import WaveTurbulence.Foundations.Molecule.VineSGNonVII
public import WaveTurbulence.Foundations.Molecule.VineOneJumpMasks
public import WaveTurbulence.Foundations.Molecule.VineSideVIILength
public import WaveTurbulence.Foundations.Molecule.VineHyperCoreProfiles
public import WaveTurbulence.Foundations.Molecule.VineHyperPrefixSuffix
public import WaveTurbulence.Foundations.Molecule.VineHyperBadTypes
public import WaveTurbulence.Foundations.Molecule.VineHyperExternalPairs
public import WaveTurbulence.Foundations.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.Molecule.VineSideBonds
public import WaveTurbulence.Foundations.Molecule.VineBlockCutFlows
public import WaveTurbulence.Foundations.Molecule.VineAdjointRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineSimultaneousAdjoints
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
public import WaveTurbulence.Foundations.Molecule.VineHyperVIIClassification
public import WaveTurbulence.Foundations.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.Molecule.VineHyperInVC
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.Molecule.VineSubsetVCVineLike
public import WaveTurbulence.Foundations.Molecule.VineSubsetVCClassification
public import WaveTurbulence.Foundations.Molecule.VinePrependSequence
public import WaveTurbulence.Foundations.Molecule.VineTypeIIMinimum
public import WaveTurbulence.Foundations.Molecule.VineCoherencePermutation
public import WaveTurbulence.Foundations.Molecule.VineSingleRailCounts
public import WaveTurbulence.Foundations.Molecule.VineSubsetVCRemoval
public import WaveTurbulence.Foundations.Molecule.VineCoherenceIndependent

/-! # Checked vine structure and coherence tools

The structural classification of ordinary and hyper vine-like subsets,
including outer DVs, and simultaneous ordinary/mixed removal are included.
The actual group partition, coherence and its index are independent of the
chosen realization. Type II
includes the one-rung four-atom Q-block (F72).
-/

public section
