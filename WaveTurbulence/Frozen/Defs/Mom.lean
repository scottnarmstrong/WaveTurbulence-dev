/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Mom

Deng–Hani, L308-L310 (inner product), L299-L307 (k in R^d). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- Momentum space `ℝ^d` with the Euclidean inner product `⟨k, ℓ⟩ = ∑ kʲ ℓʲ` (DH (COL), §1.1). -/
abbrev Mom (d : ℕ) := EuclideanSpace ℝ (Fin d)

end WaveTurbulence
