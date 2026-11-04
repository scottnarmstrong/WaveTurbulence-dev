/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# timeFT

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- The time Fourier transform `F̂(λ, v) = ∫ F(t, v) e^{-2πi⟨λ,t⟩} dt` in `r` time variables. -/
noncomputable def timeFT {r : ℕ} {V : Type*} (F : (Fin r → ℝ) → V → ℂ) (lam : Fin r → ℝ) (v : V) :
    ℂ :=
  ∫ t : Fin r → ℝ, F t v * Complex.exp (-(2 * Real.pi * ∑ i, lam i * t i : ℝ) * Complex.I)

end Norms
end WaveTurbulence
