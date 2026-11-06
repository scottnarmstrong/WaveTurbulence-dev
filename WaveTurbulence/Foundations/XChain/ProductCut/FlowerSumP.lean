/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FlowerSumP
public import WaveTurbulence.Frozen.Defs.FlowerSum
public import WaveTurbulence.Frozen.Defs.OmegaNode
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.LayeredGardenOnStem
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableOnStem
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsFlowerNode
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsTopLeaf

/-!
# The uncut successor flower sum

D13 freezes `flowerSumP` with product-form weights. Its uncut clause is definitionally unchanged.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.XChain.ProductCut

/-- The successor clause equals the frozen one when no cutoff is inserted. -/
theorem flowerSumP_none (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerSumP P F p N kind pat dagger none none ζ t s n n' =
      flowerSum P F p N kind pat dagger none none ζ t s n n' := rfl

end WaveTurbulence.XChain.ProductCut
