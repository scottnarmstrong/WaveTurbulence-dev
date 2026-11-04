/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Chi0Vec
public import WaveTurbulence.Frozen.Defs.EZ
public import WaveTurbulence.Foundations.WeylSums.MinorArcSums

/-!
# The landed Weyl-sum carriers are the frozen ones

The landed lattice sums of TARGET Lemma 5.3 and `lemcubic` (`bilinearLatticeSum`, `cubicLatticeSum`) are built
from `latticeCutoff` and `e`. The frozen anchors `quadExpSum2` and `quadExpSum3` (ruling D7) are stated with the
frozen `chi0Vec` and `eZ`. These two identities make the landed statements the anchors' statements.
-/

public section

namespace WaveTurbulence.WeylSums

/-- The frozen vector cutoff is the landed tensor-product cutoff. -/
theorem chi0Vec_eq_latticeCutoff {d : ℕ} (x : Mom d) : chi0Vec x = latticeCutoff x := by
  simp only [chi0Vec, latticeCutoff, chi0_eq_draft_formula, chi0]

/-- The frozen phase `eZ` is the landed `e`. -/
theorem eZ_eq_e (z : ℝ) : eZ z = e z := rfl

end WaveTurbulence.WeylSums
