/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.FrequencySplit

/-!
# Link masses after finitely many trivial replacements

TARGET (incohproof18), (incohproof25)–(incohproof27): replacing a chosen
link means inserting its proved trivial lattice bound; every other link
keeps its actual integrated mass.
-/

public section
noncomputable section
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The literal mass used after a finite selected set of links is replaced by trivial bounds. -/
@[expose] def replacedLinkMass {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (J : Finset (Fin n)) (i : Fin n) : ℝ≥0∞ :=
  if i ∈ J then ENNReal.ofReal ((5 * L) ^ (2 * d)) else layerLinkMass L (δ * L ^ (2 * γ)) (Q i)

end WaveTurbulence.Incoh
