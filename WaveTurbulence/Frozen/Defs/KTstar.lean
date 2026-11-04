/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.KernelK
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# KTstar

Wave B tier B1 (WaveB1-System.lean), source: T (timepairtree), L681–L684. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- **`K*_𝒯(t, s, k)`** (T (timepairtree), L681–L684) for a layered paired tree (`IsPairedTree`):
coset `k`-decorations (`k_𝔯 = k_{ℓ_lo} = k`), all times `< t`, the parent of the lone leaf `> s`, the
input product over `+` leaves other than the lone leaf. -/
noncomputable def KTstar (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelK L γ δ F LG (fun _ => t) s k (fun _ => 0) 0

end Kernels
end WaveTurbulence
