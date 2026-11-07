/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # Exact finite-fiber counting for DH23's degenerate-atom removal -/

@[expose] public section
set_option autoImplicit false
open Finset

namespace WaveTurbulence.Degen

variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The literal common-label condition at a degenerate/tame atom. -/
def ConstantAt (M : Molecule V D) (κ : D → K) (v : V) : Prop :=
  ∀ x ∈ M.dartsAt v, ∀ y ∈ M.dartsAt v, κ x = κ y

/-- Every label removed with a constant atom is its common label, even
at the dart on the other end of the deleted bond. -/
theorem removed_value_eq_common (M : Molecule V D) {κ : D → K} {v : V} {e x : D}
    (hκ : ∀ y, κ (M.mate y) = κ y) (hc : ConstantAt M κ v) (he : M.atom e = v)
    (hx : M.atom x = v ∨ M.atom (M.mate x) = v) : κ x = κ e := by
  have he' : e ∈ M.dartsAt v := by simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]; exact he
  rcases hx with hx | hx
  · exact hc x (by simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]; exact hx) e he'
  · rw [← hκ x]
    exact hc (M.mate x) (by simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]; exact hx) e he'

/-- A decoration is recovered from its common removed label and its actual
restriction to retained bonds. This proves the counting step, not an
assumed estimate for either side. -/
theorem removal_pair_injective (M : Molecule V D) {v : V} {e : D} (he : M.atom e = v)
    {κ κ' : D → K} (hκ : ∀ y, κ (M.mate y) = κ y) (hκ' : ∀ y, κ' (M.mate y) = κ' y)
    (hc : ConstantAt M κ v) (hc' : ConstantAt M κ' v)
    (hpair : (κ e, fun x : RetainedDart M {v} => κ x.val) =
      (κ' e, fun x : RetainedDart M {v} => κ' x.val)) : κ = κ' := by
  classical
  have heq : κ e = κ' e := congrArg Prod.fst hpair
  have hrest := congrArg Prod.snd hpair
  funext x
  by_cases hx : M.atom x = v ∨ M.atom (M.mate x) = v
  · exact (removed_value_eq_common M hκ hc he hx).trans
      (heq.trans (removed_value_eq_common M hκ' hc' he hx).symm)
  · have hx' : M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v := not_or.mp hx
    exact congrFun hrest ⟨x, by simpa only [mem_singleton] using hx'.1,
      by simpa only [mem_singleton] using hx'.2⟩

/-- DH23 section 10.5(4), exact finite counting form: common-label choices
times actual restricted-label choices bound the original count. -/
theorem card_le_common_mul_restriction [DecidableEq K] (M : Molecule V D) {v : V} {e : D}
    (he : M.atom e = v) (S : Finset (D → K))
    (hb : ∀ κ ∈ S, ∀ x, κ (M.mate x) = κ x)
    (hc : ∀ κ ∈ S, ConstantAt M κ v) :
    S.card ≤ (S.image (fun κ => κ e)).card *
      (S.image (fun κ => fun x : RetainedDart M {v} => κ x.val)).card := by
  classical
  let f := fun κ : D → K => (κ e, fun x : RetainedDart M {v} => κ x.val)
  have hinj : Set.InjOn f S := by
    intro κ hκ κ' hκ' heq
    exact removal_pair_injective M he (hb κ hκ) (hb κ' hκ') (hc κ hκ) (hc κ' hκ') heq
  calc
    _ = (S.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((S.image (fun κ => κ e)) ×ˢ
        (S.image (fun κ => fun x : RetainedDart M {v} => κ x.val))).card := by
      apply card_le_card
      intro p hp
      obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨mem_image.mpr ⟨κ, hκ, rfl⟩, mem_image.mpr ⟨κ, hκ, rfl⟩⟩
    _ = _ := card_product _ _

end WaveTurbulence.Degen
