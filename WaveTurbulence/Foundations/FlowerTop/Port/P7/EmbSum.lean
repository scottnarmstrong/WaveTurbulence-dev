/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! FLOWER-P7: an abstract lemma on equivalence-class sums transported along an injection
(used for `attachedOrder` through the cap and the glue). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7

theorem eqvGen_embedding {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (RA : α → α → Prop) (RB : β → β → Prop) (hR : ∀ a b, RB (f a) (f b) ↔ RA a b)
    (hRB : ∀ x y, RB x y → (x ∈ Set.range f ↔ y ∈ Set.range f)) (a : α) (z : β) :
    Relation.EqvGen RB (f a) z ↔ ∃ b, z = f b ∧ Relation.EqvGen RA a b := by
  constructor
  · intro h
    have key : ∀ x y, Relation.EqvGen RB x y →
        (x ∈ Set.range f ↔ y ∈ Set.range f) ∧ ∀ a b, x = f a → y = f b → Relation.EqvGen RA a b := by
      intro x y hxy
      induction hxy with
      | rel x y hr =>
        refine ⟨hRB x y hr, ?_⟩
        rintro a b rfl rfl
        exact Relation.EqvGen.rel _ _ ((hR a b).1 hr)
      | refl x =>
        refine ⟨Iff.rfl, ?_⟩
        rintro a b rfl h
        have := hf h
        subst this
        exact Relation.EqvGen.refl _
      | symm x y _ ih =>
        refine ⟨ih.1.symm, ?_⟩
        rintro a b rfl rfl
        exact Relation.EqvGen.symm _ _ (ih.2 b a rfl rfl)
      | trans x y z _ _ ih1 ih2 =>
        refine ⟨ih1.1.trans ih2.1, ?_⟩
        rintro a c rfl rfl
        obtain ⟨b, hb⟩ := ih1.1.1 ⟨a, rfl⟩
        exact Relation.EqvGen.trans _ _ _ (ih1.2 a b rfl hb.symm) (ih2.2 b c hb.symm rfl)
    obtain ⟨hiff, hk⟩ := key _ _ h
    obtain ⟨b, hb⟩ := hiff.1 ⟨a, rfl⟩
    exact ⟨b, hb.symm, hk a b rfl hb.symm⟩
  · rintro ⟨b, rfl, h⟩
    induction h with
    | rel x y hr => exact Relation.EqvGen.rel _ _ ((hR _ _).2 hr)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

open scoped Classical in
theorem sum_filter_eqvGen_embedding {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (SA : Finset α) (SB : Finset β) (hS : ∀ x, f x ∈ SB ↔ x ∈ SA)
    (RA : α → α → Prop) (RB : β → β → Prop) (hR : ∀ a b, RB (f a) (f b) ↔ RA a b)
    (hRB : ∀ x y, RB x y → (x ∈ Set.range f ↔ y ∈ Set.range f)) (wA : α → ℕ) (wB : β → ℕ)
    (hw : ∀ a, wB (f a) = wA a) (u : α) :
    ∑ u' ∈ SB.filter (fun u' => Relation.EqvGen RB (f u) u'), wB u' =
      ∑ u' ∈ SA.filter (fun u' => Relation.EqvGen RA u u'), wA u' := by
  classical
  have himg : SB.filter (fun u' => Relation.EqvGen RB (f u) u') =
      (SA.filter (fun u' => Relation.EqvGen RA u u')).image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hy, h⟩
      obtain ⟨b, rfl, hb⟩ := (eqvGen_embedding f hf RA RB hR hRB u y).1 h
      exact ⟨b, ⟨(hS b).1 hy, hb⟩, rfl⟩
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      exact ⟨(hS b).2 hb1, (eqvGen_embedding f hf RA RB hR hRB u (f b)).2 ⟨b, rfl, hb2⟩⟩
  rw [himg, Finset.sum_image (fun x _ y _ h => hf h)]
  exact Finset.sum_congr rfl fun a _ => hw a

end WaveTurbulence.FlowerP7
