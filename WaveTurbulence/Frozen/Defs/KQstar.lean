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
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# KQstar

Wave B tier B1 (WaveB1-System.lean), source: T (timecouple), L678–L680. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- **`K*_𝒬(t, s, k)`** (T (timecouple), L678–L680) for a layered couple and `k ∈ ℝ^d`: coset
`k`-decorations, `𝒯⁺` times `< t`, `𝒯⁻` times `< s`. -/
noncomputable def KQstar (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelK L γ δ F LG (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0

end Kernels
end WaveTurbulence
