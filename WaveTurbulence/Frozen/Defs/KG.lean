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
# KG

Wave B tier B1 (WaveB1-System.lean), source: T (defkg0), L671–L674. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- **`K_𝒢(t, n₁,…,n_w)`** (T (defkg0), L671–L674): lattice decorations with root labels `n_j`. -/
noncomputable def KG (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (t : ℝ)
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  kernelK L γ δ F LG (fun _ => t) 0 0 n 0

end Kernels
end WaveTurbulence
