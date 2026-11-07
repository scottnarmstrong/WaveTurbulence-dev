/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.Vine.A.VineFineIngredients
public import WaveTurbulence.Foundations.Vine.A.VineIngredientCarrier
public import WaveTurbulence.Foundations.Vine.A.VineBadCount
public import WaveTurbulence.Foundations.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.Vine.A.VinePrimeUnique
public import WaveTurbulence.Foundations.Vine.A.VineBatchFamily
public import WaveTurbulence.Foundations.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
public import WaveTurbulence.Foundations.Vine.A.VineOperationReindex
public import WaveTurbulence.Foundations.Vine.A.VineEmptyOrbit
public import WaveTurbulence.Foundations.Vine.A.VineSpliceOrder
public import WaveTurbulence.Foundations.Vine.A.VineSpliceParents
public import WaveTurbulence.Foundations.Vine.A.VineCoarseBatch
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDartEquiv
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceTimeDomain
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceEpsilon
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceTimeIntegral
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceKernel
public import WaveTurbulence.Foundations.Vine.A.VineOperationPieceData
public import WaveTurbulence.Foundations.Vine.A.VineCollectionGeometry
public import WaveTurbulence.Foundations.Vine.A.VineTauGardenFibres
public import WaveTurbulence.Foundations.Vine.A.VineHingeGapTransport
public import WaveTurbulence.Foundations.Vine.A.VineHVCGroupGap
public import WaveTurbulence.Foundations.Vine.A.VineHVChoiceExample
public import WaveTurbulence.Foundations.Vine.A.VineBatchTreeIndex
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.Vine.A.VinePortRigidity
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesigCovariance
public import WaveTurbulence.Foundations.Vine.A.VineProducer
/-! VINE-A R83 exports: exact ordered normalization through the actual splice
fold, normalized HV/DV successor designations, the full fixed-sigma partition
on plain gardens, and A4 with the complete actual gap functional. C1 indices
have explicit support/joint/tag correspondences; actual hinge-pair gap kinds
and the literal kernel value are preserved. Successor producer definitions
live in VineA.NormalizedSplice. S2/P6 integration is owned by those packets. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
