/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# jointCumulant

Wave B tier B1 (WaveB1-System.lean), source: T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **The joint cumulant** `𝕂((X_j)_{j ∈ s})` of T Def `defcm` (eqncm), expectations against a measure
`μ` (`μ = P.restrict F` for "assuming `F`"): the sum over all partitions `𝒫` of `s` of
`(-1)^{|𝒫|-1} (|𝒫|-1)! ∏_{A ∈ 𝒫} 𝔼 ∏_{j ∈ A} X_j`. Same body as the landed `cumulant` (CUMUL packet;
bridge `jointCumulant_eq_cumulant`). -/
noncomputable def jointCumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω)
    (X : ι → Ω → ℂ) (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
    ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ

end WaveTurbulence
