/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.XNorm00

/-!
# XNorm00Restr

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

noncomputable def XNorm00Restr {r : ℕ} {V : Type*} (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → V → ℂ) (_ : ∀ t ∈ B, ∀ v ∈ K, G t v = F t v), XNorm00 θ G

end Norms
end WaveTurbulence
