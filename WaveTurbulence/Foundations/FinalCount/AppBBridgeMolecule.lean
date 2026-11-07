/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeCounting
import Mathlib.Tactic

/-! # Bond deletion preserves the complete molecule axioms and large gaps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_eraseBond_direction_card_le (M : Molecule V D) (e : D) (v : V) (b : Bool) :
    ((((eraseBond M e).dartsAt v).filter (fun x => (eraseBond M e).out x = b)).card) ≤
      (((M.dartsAt v).filter (fun x => M.out x = b)).card) := by
  apply card_le_card_of_injOn (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => x.val)
  · intro x hx
    obtain ⟨hx,hb⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,hb⟩
  · intro x hx y hy he
    exact Subtype.ext he

theorem appb_eraseBond_isMolecule (M : Molecule V D) (hM : M.IsMolecule) (e : D) :
    (eraseBond M e).IsMolecule := by
  classical
  let N := eraseBond M e
  constructor
  · intro v hv
    exact ⟨(appb_eraseBond_direction_card_le M e v true).trans (hM.1 v hv).1,
      (appb_eraseBond_direction_card_le M e v false).trans (hM.1 v hv).2⟩
  · intro v hv
    by_contra hn
    push_neg at hn
    let S := Degen.componentSet N v
    have hS : S ⊆ M.atoms := by
      intro u hu
      exact ((Degen.mem_componentSet N v u).mp hu).1
    have hne : S.Nonempty := ⟨v,(Degen.mem_componentSet N v v).mpr ⟨hv,Relation.EqvGen.refl _⟩⟩
    apply no_saturated_group M hM hS hne
    intro u hu
    have huN := (Degen.mem_componentSet N v u).mp hu
    have hd : N.deg u = 4 := hn u huN.1 huN.2
    have hle : N.deg u ≤ M.degIn S u := by
      apply card_le_card_of_injOn (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => x.val)
      · intro x hx
        have hxu : N.atom x = u := (mem_filter.mp hx).2
        have hmate : N.atom (N.mate x) ∈ S := by
          apply (Degen.mem_componentSet N v _).mpr
          exact ⟨N.atom_mem _,Relation.EqvGen.trans _ _ _ huN.2 (Relation.EqvGen.rel _ _ ⟨x,hxu,rfl⟩)⟩
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hxu⟩,hxu.symm ▸ hu,hmate⟩
      · intro x hx y hy he
        exact Subtype.ext he
    have hh := deg_le_four M hM (hS hu)
    have hi := degIn_le_deg M S u
    omega

theorem appb_eraseBond_largeGap (M : Molecule V D) (e : D) {d : ℕ}
    {L g : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} (h : AppbLargeGap M L w κ g) :
    AppbLargeGap (eraseBond M e) L w (fun x => κ x.val) g := by
  intro v hv x hx y hy hdir hmate
  have hx' : x.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have hy' : y.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
  exact h v hv x.val hx' y.val hy' hdir (fun he => hmate (Subtype.ext he))

end WaveTurbulence.Mole
