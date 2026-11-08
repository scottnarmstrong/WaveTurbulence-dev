/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Defs
public import WaveTurbulence.Foundations.Flower.Stage1W.TypeBound
public import WaveTurbulence.Foundations.RegularAsymptotics.PairedTreeContinuity
public import WaveTurbulence.Foundations.VineEst.RowSel.Analytic

/-! # V5W-0, row 0a: the analytic API of the incoherent rows `coupleLeavesTop` / `treeLeavesTop`

The whole API (`norm_topPsi_le`, `norm_rowTopWeight_le`, `norm_kernelLeavesW_summand_le`,
`continuous_kernelLeavesW_layer`, `continuous_coupleLeavesTop_time`, `continuous_treeLeavesTop_time`,
`norm_kernelLeavesW_layer_le`, `rowTopWeight_one`, `kernelLeavesW_one`, `coupleLeavesTop_one`, `treeLeavesTop_one`,
namespace `WaveTurbulence.Flower.V5W`) is now on main (416902c8, V5W-B: `VineEst/RowSel/Analytic.lean`, the same text).
This module only re-exports it, so that world importers need no edit.
-/
