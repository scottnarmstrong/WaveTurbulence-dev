/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# LatticePoint

Deng–Hani, L286. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The lattice point `k = n / L ∈ ℤ_L^d = (L⁻¹ ℤ)^d` of the dual torus (DH §1.1). -/
def latticePoint {d : ℕ} (L : ℝ) (n : Fin d → ℤ) : Mom d :=
  WithLp.toLp 2 (fun j => (n j : ℝ) / L)

end WaveTurbulence
