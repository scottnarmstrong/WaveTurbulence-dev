/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeGraphEffects
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # A bridge is a single bond and its actual post endpoints disconnect -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bridge_endpoints_not_post_connected (M : Molecule V D) (e : D)
    (hb : Degen.IsBridge M e) :
    ¬(eraseBond M e).SameComponent (M.atom e) (M.atom (M.mate e)) := by
  have hlift : ∀ a b,(eraseBond M e).SameComponent a b →
      Relation.EqvGen (Degen.AdjWithoutBond M e) a b := by
    intro a b hp
    induction hp with
    | rel a b h =>
      obtain ⟨x,hx,hy⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨x.val,hx,hy,x.property⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b hp ih => exact ih.symm
    | trans a b c hp hp' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  exact fun hp => hb (hlift _ _ hp)

theorem bridge_multiplicity_eq_one (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    M.bondsBetween (M.atom e) (M.atom (M.mate e)) = 1 := by
  classical
  have hne := appb_bridge_endpoints_distinct M e hb
  rw [bondsBetween_eq_card_darts M hne]
  have hs : (M.dartsAt (M.atom e)).filter (fun x => M.atom (M.mate x) = M.atom (M.mate e)) = {e} := by
    ext x
    simp only [mem_filter,mem_dartsAt,mem_singleton]
    constructor
    · rintro ⟨hx,hxm⟩
      by_contra hxe
      have hxme : x ≠ M.mate e := by
        intro he
        exact hne (hx.symm.trans (congrArg M.atom he))
      exact hb (Relation.EqvGen.rel _ _ ⟨x,hx,hxm,hxe,hxme⟩)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  rw [hs,card_singleton]

end WaveTurbulence.Mole.AppbAlgorithm
