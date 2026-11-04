/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeOrder
public import WaveTurbulence.Frozen.Defs.TreeTerm

/-!
# treeTermN

Wave B tier B1 (WaveB1-System.lean), source: T (defjn). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- `𝒥_N = ∑_{n(𝒯) = N} 𝒥_𝒯` over trees of sign `+` (T (defjn)); a finite sum. -/
noncomputable def treeTermN (p N : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ᶠ (T : TTree) (_ : T.order = N), treeTerm L γ δ p T b t n

end Duhamel
end WaveTurbulence
