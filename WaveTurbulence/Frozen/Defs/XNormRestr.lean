/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.XNorm

/-!
# XNormRestr

Wave B tier B1 (WaveB1-System.lean), source: T (locnorm), L589. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- **Restriction norms** (T (locnorm), L589): the infimum of the norms of all `G` agreeing with `F`
on `ℬ × K` (`⊤` if there is none). -/
noncomputable def XNormRestr {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → Mom d → ℂ) (_ : ∀ t ∈ B, ∀ k ∈ K, G t k = F t k), XNorm θ Λ₁ Λ₂ G

end Norms
end WaveTurbulence
