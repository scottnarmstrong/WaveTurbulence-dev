/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TreeTermN

/-!
# aTr

Wave B tier B1 (WaveB1-System.lean), source: T (defbk). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- `a^tr = ∑_{N ≤ Ntr} 𝒥_N` (T (defbk); `Ntr = N_{p+1}`). -/
noncomputable def aTr (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ N ∈ Finset.range (Ntr + 1), treeTermN L γ δ p N b t n

end Duhamel
end WaveTurbulence
