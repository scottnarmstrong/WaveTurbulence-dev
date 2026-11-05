/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # Port shim (REDSPLICE): two garden pairing lemmas that the MOLE-universe draft stated separately
and that the canonical B2 `Molecules` inlines. Statements are the MOLE ones. -/

public section
namespace WaveTurbulence
variable {w : ℕ}

theorem Garden.pair_ne_of_unmarked {G : Garden w} {ℓ : GLeaf G.tree} (h : G.mark ℓ = none) :
    G.pair ℓ ≠ ℓ := fun he => ((G.pair_eq_iff ℓ).1 he) h

theorem Garden.pair_unmarked {G : Garden w} {ℓ : GLeaf G.tree} (h : G.mark ℓ = none) :
    G.mark (G.pair ℓ) = none := by
  by_contra hm
  have h1 := (G.pair_eq_iff (G.pair ℓ)).2 hm
  rw [G.pair_pair] at h1
  exact ((G.pair_eq_iff ℓ).1 h1.symm) h

end WaveTurbulence
