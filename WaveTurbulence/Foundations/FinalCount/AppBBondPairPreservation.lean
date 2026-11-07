/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondErasure
import Mathlib.Tactic

/-! # Bond deletion preserves every unaffected endpoint pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_ends_mate (M : Molecule V D) (x : D) : M.ends (M.mate x) = M.ends x := by
  apply Sym2.eq_iff.mpr
  exact Or.inr ⟨rfl,congrArg M.atom (M.mate_mate x)⟩

theorem appb_eraseBond_bondsBetween_eq (M : Molecule V D) (e : D) (a b : V)
    (hne : M.ends e ≠ s(a,b)) : (eraseBond M e).bondsBetween a b = M.bondsBetween a b := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    have ho : M.out x.val = true := (mem_filter.mp hx).2
    change M.ends x.val = s(a,b) at he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,he⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    have hxe : x ≠ e := by intro hh; exact hne (hh ▸ he)
    have hxm : x ≠ M.mate e := by
      intro hh
      rw [hh,appb_ends_mate] at he
      exact hne he
    refine ⟨⟨x,hxe,hxm⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,he⟩

theorem appb_eraseBond_directed_iff (M : Molecule V D) (e : D) (a b : V)
    (hne : M.ends e ≠ s(a,b)) : (eraseBond M e).Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨x,ho,ha,hb⟩
    exact ⟨x.val,ho,ha,hb⟩
  · rintro ⟨x,ho,ha,hb⟩
    have he : M.ends x = s(a,b) := by simp only [Molecule.ends,ha,hb]
    have hxe : x ≠ e := by intro hh; exact hne (hh ▸ he)
    have hxm : x ≠ M.mate e := by
      intro hh
      rw [hh,appb_ends_mate] at he
      exact hne he
    exact ⟨⟨x,hxe,hxm⟩,ho,ha,hb⟩

end WaveTurbulence.Mole
