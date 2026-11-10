/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Characterization
public import WaveTurbulence.Foundations.WKE.Trilinear

/-!
# The resonant integral

The two deltas in TARGET (C.5) and DH21 Proposition 7.7 (L1814–L1837) are read
using the hyperplane measure fixed by D6. The kernel takes the three momenta
as separate arguments. `tendsto_mollified_resonantIntegral_k` characterizes this
reading by mollification of the energy delta, including its negative sign.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- The kernel after eliminating momentum conservation and translating by `k`. -/
@[expose] def resonantKernel (Ψ : Mom d → Mom d → Mom d → ℝ) (k ℓ x : Mom d) : ℝ :=
  Ψ (k + ℓ) (k + ℓ + x) (k + x)

end WaveTurbulence.Resonant
