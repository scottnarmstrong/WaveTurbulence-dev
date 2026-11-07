/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorBridge
/-! R94: both members of an anchored pair have profile one. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.S2ST
open LGSpine FlowerX7X5

/-- R94's both-member convention, including an anchor root when it is the counted input.
The condition is on all actual leaves, with no sign or input-leaf restriction. -/
def AnchorOneBoth {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (H : LeafProfiles w d) : Prop :=
  ∀ a : GLeaf LG.garden.tree, a.1.1 ∈ J ∨ (LG.garden.pair a).1.1 ∈ J →
    H a.1 = fun _ => 1

theorem AnchorOneBoth.toAnchorOne {w d : ℕ} {LG : LayeredGarden w}
    {J : Finset (Fin w)} {H : LeafProfiles w d} (h : AnchorOneBoth LG J H) :
    FlowerP1.AnchorOne LG J H := by
  intro a _ ha
  exact h a (Or.inr ha.2)

theorem anchoredProfiles_anchorOneBoth {w d : ℕ} (LG : LayeredGarden w)
    (J : Finset (Fin w)) (h : PairProfile (LeafPairType w) d) :
    AnchorOneBoth LG J (anchoredProfiles LG J h) := by
  intro a ha
  funext x
  rw [anchoredProfiles_leaf]
  exact ite_eq_left ha

theorem anchorOneBoth_empty {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d) :
    AnchorOneBoth LG ∅ H := by
  intro a ha
  exact (ha.elim (Finset.notMem_empty _) (Finset.notMem_empty _)).elim
end WaveTurbulence.S2ST
