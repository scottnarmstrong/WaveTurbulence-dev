/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Bridge333SpecialTransport
import Mathlib.Tactic

/-! # Exact special-bond count decrement for BR333 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bridge333_special_count_eq_erase (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (appbSpecialBonds (eraseBond M e)).card = ((appbSpecialBonds M).erase e).card := by
  classical
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have hs := (bridge333_retained_special_iff M hno e hb hout h1 h2 x).mp (mem_filter.mp hx).2
    exact mem_erase.mpr ⟨x.property.1,mem_filter.mpr ⟨mem_univ _,hs⟩⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hne,hx⟩ := mem_erase.mp hx
    have hs := (mem_filter.mp hx).2
    have hnm : x ≠ M.mate e := by
      intro he
      have hh := congrArg M.out he
      rw [hs.1,M.out_mate,hout] at hh
      cases hh
    let y : {x : D // x ≠ e ∧ x ≠ M.mate e} := ⟨x,hne,hnm⟩
    exact ⟨y,mem_filter.mpr ⟨mem_univ _,
      (bridge333_retained_special_iff M hno e hb hout h1 h2 y).mpr hs⟩,rfl⟩

open Classical in
/-- Source BR333 removes exactly its own possible special bond and
creates none. This includes the nonspecial bridge case. -/
theorem bridge333_special_count (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (appbSpecialBonds (eraseBond M e)).card+(if AppbSpecial M e then 1 else 0) =
      (appbSpecialBonds M).card := by
  classical
  rw [bridge333_special_count_eq_erase M hno e hb hout h1 h2]
  by_cases hs : AppbSpecial M e
  · rw [if_pos hs]
    exact card_erase_add_one (mem_filter.mpr ⟨mem_univ _,hs⟩)
  · rw [if_neg hs,add_zero,erase_eq_of_notMem]
    simpa only [appbSpecialBonds,mem_filter,mem_univ,true_and] using hs

end WaveTurbulence.Mole.AppbAlgorithm
