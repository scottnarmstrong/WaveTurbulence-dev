/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SameTree

/-! # Order and per-tree layer counts for the collapsed LF unit

The same-tree hypothesis is geometric: designated source CL placements satisfy
it by `placement_same_tree`. It cannot be dropped for arbitrary placements.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w) (P : CorePlacement LG.garden)

/-- Once total order bounds all attached components, truncation tests only top trees. -/
theorem trunc_iff_topOrder (LG : LayeredGarden w) (p Ntop Natt : ℕ)
    (hn : LG.garden.order ≤ Natt) :
    LG.IsTrunc p Ntop Natt ↔ ∀ j, LG.topOrder p j ≤ Ntop := by
  exact ⟨And.left, fun h => ⟨h, fun u _ => (LG.attachedOrder_le_order p u).trans hn⟩⟩

end WaveTurbulence.LFTwist
