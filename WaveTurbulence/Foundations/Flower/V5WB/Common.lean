/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.K.Defs
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedMerge
public import WaveTurbulence.Foundations.VineEst.VineSpaceB.BondStatements

/-! # V5W-B-WORLD: the selector-free V5-SPACE(-EXT) declarations reused by import

V5W-A's port of V5-SPACE-EXT is compiled at the plain selector.  Its selector-free declarations (molecule darts and
bond labels, engine pullbacks and character mixtures, `TermCertW` products, `layX`; checked by the dependency probe
recorded in `PROGRESS.md`) are reused by import; the selector-dependent modules are copied into `Flower/V5WB/K`,
`Flower/V5WB/B` with the selector as a variable. -/
