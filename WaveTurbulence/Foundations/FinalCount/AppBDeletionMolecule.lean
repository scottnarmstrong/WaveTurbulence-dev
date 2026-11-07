/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Literal atom deletion preserves the full molecule axioms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_eraseAtoms_direction_card_le (M : Molecule V D) (Y : Finset V) (v : V) (b : Bool) :
    (((Degen.eraseAtoms M Y).dartsAt v).filter (fun x => (Degen.eraseAtoms M Y).out x = b)).card ≤
      ((M.dartsAt v).filter (fun x => M.out x = b)).card := by
  apply Finset.card_le_card_of_injOn (fun x : Degen.RetainedDart M Y => x.val)
  · intro x hx
    obtain ⟨hx,hb⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,hb⟩
  · intro x hx y hy he
    exact Subtype.ext he

/-- A saturated component after deletion would give a nonempty saturated
atomic group in the old molecule. Thus the nonsaturation axiom is proved,
not retained as an extra postcondition. -/
theorem appb_eraseAtoms_isMolecule (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V) :
    (Degen.eraseAtoms M Y).IsMolecule := by
  classical
  let N := Degen.eraseAtoms M Y
  constructor
  · intro v hv
    have hvM := (mem_sdiff.mp hv).1
    exact ⟨(appb_eraseAtoms_direction_card_le M Y v true).trans (hM.1 v hvM).1,
      (appb_eraseAtoms_direction_card_le M Y v false).trans (hM.1 v hvM).2⟩
  · intro v hv
    by_contra hn
    push_neg at hn
    let S := Degen.componentSet N v
    have hS : S ⊆ M.atoms := by
      intro u hu
      exact (mem_sdiff.mp ((Degen.mem_componentSet N v u).mp hu).1).1
    have hne : S.Nonempty := ⟨v,(Degen.mem_componentSet N v v).mpr ⟨hv,Relation.EqvGen.refl v⟩⟩
    apply no_saturated_group M hM hS hne
    intro u hu
    have huN := (Degen.mem_componentSet N v u).mp hu
    have hd : N.deg u = 4 := hn u huN.1 huN.2
    have hle : N.deg u ≤ M.degIn S u := by
      apply Finset.card_le_card_of_injOn (fun x : Degen.RetainedDart M Y => x.val)
      · intro x hx
        have hxu : N.atom x = u := (mem_filter.mp hx).2
        have hmate : N.atom (N.mate x) ∈ S := by
          apply (Degen.mem_componentSet N v _).mpr
          refine ⟨N.atom_mem _,Relation.EqvGen.trans _ _ _ huN.2 ?_⟩
          exact Relation.EqvGen.rel _ _ ⟨x,hxu,rfl⟩
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hxu⟩,hxu.symm ▸ hu,hmate⟩
      · intro x hx y hy he
        exact Subtype.ext he
    have hdeg := deg_le_four M hM (hS hu)
    have hdegIn := degIn_le_deg M S u
    omega

theorem appb_eraseAtoms_noLoops (M : Molecule V D) (Y : Finset V) (h : AppbNoLoops M) :
    AppbNoLoops (Degen.eraseAtoms M Y) := fun x => h x.val

theorem appb_eraseAtoms_noTripleBonds (M : Molecule V D) (Y : Finset V)
    (h : AppbNoTripleBonds M) : AppbNoTripleBonds (Degen.eraseAtoms M Y) := by
  intro a ha b hb hne
  have ha' := mem_sdiff.mp ha
  have hb' := mem_sdiff.mp hb
  rw [Degen.bondsBetween_erase_eq M Y ha'.2 hb'.2]
  exact h a ha'.1 b hb'.1 hne

end WaveTurbulence.Mole
