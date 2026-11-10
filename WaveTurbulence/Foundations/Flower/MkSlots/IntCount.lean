/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntPiece
public import WaveTurbulence.Foundations.Spine.InputLeafCount

/-! # B3s MK-SLOTS (integration): the anchored leaf count (the mass `b ^ N`)

In a plain garden of order `N` with `2R` trees there are `N + R` input leaves (one per leaf pair, main's
`twice_card_inputLeaves`). The anchored profile `1` sits on the input leaves of the pairs meeting a cap tree. When the
cap trees are single leaves and no two cap roots are paired, there is exactly one such input leaf per cap tree
(`card_anchoredInputs`), so with `J.card = R` the free input leaves number `N` (`card_freeInputs`): the class value is
of degree `N` in the profiles, matching the mass `b ^ N` (F-B3s-8). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- The leaf of a single-leaf tree. -/
def rootLeaf (G : Garden w) (j : Fin w) (hj : G.tree j = TTree.leaf) : GLeaf G.tree :=
  ⟨(j, []), by rw [hj]; simp [TTree.leaves]⟩

theorem eq_rootLeaf {G : Garden w} {j : Fin w} (hj : G.tree j = TTree.leaf) (ℓ : GLeaf G.tree) (hℓ : ℓ.1.1 = j) :
    ℓ = rootLeaf G j hj := by
  have hl := ℓ.2
  rw [hℓ, hj] at hl
  have hp : ℓ.1.2 = [] := by simpa [TTree.leaves] using hl
  exact Subtype.ext (Prod.ext hℓ hp)

end WaveTurbulence.Flower.MkSlots
