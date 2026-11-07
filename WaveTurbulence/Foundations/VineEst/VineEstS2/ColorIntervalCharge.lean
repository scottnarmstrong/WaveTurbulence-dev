/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # At most two sign-skipping predecessor intervals can cover one node -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- An ancestor interval stops before its next occurrence of the start color.
Heavy-path reachability is an additional restriction, so cannot increase the
number of such intervals passing through a fixed tree node. -/
def ColorInterval {α : Type*} (R : α → α → Prop) (color : α → Bool) (a b : α) : Prop :=
  R a b ∧ ∀ z, R a z → R z b → a ≠ z → color z ≠ color a

/-- Ancestors of a tree node are linearly ordered. Consequently the color of
a start vertex identifies it uniquely among intervals covering that node. -/
theorem colorInterval_start_injective {α : Type*} (R : α → α → Prop) (color : α → Bool)
    (w a b : α)
    (compare : R a w → R b w → R a b ∨ R b a)
    (ha : ColorInterval R color a w) (hb : ColorInterval R color b w)
    (hc : color a = color b) : a = b := by
  by_contra hne
  rcases compare ha.1 hb.1 with hab | hba
  · exact ha.2 b hab hb.1 hne hc.symm
  · exact hb.2 a hba ha.1 (Ne.symm hne) hc

/-- The two-sign charge bound used to turn signed child identities into
subtraction-only sumint predecessor rows. -/
theorem card_colorInterval_starts_le_two {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (color : α → Bool)
    (w : α) (S : Finset α)
    (compare : ∀ a b, R a w → R b w → R a b ∨ R b a)
    (hS : ∀ a ∈ S, ColorInterval R color a w) : S.card ≤ 2 := by
  have hi : Set.InjOn color S := by
    intro a ha b hb hc
    exact colorInterval_start_injective R color w a b (compare a b) (hS a ha) (hS b hb) hc
  calc
    S.card = (S.image color).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := Fintype.card_bool

end WaveTurbulence.VineEstS2
