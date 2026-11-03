/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# KineticTime

Deng–Hani, L297. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The kinetic (Van Hove) time `T_kin = 1 / (2α²)` (DH §1.1, L297). -/
def kineticTime (α : ℝ) : ℝ := 1 / (2 * α ^ 2)

end WaveTurbulence
