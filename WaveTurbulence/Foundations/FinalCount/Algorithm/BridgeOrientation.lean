/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
import Mathlib.Tactic

/-! # Outgoing bridge selection and inherited no-triple exclusion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem isBridge_mate_iff (M : Molecule V D) (e : D) :
    Degen.IsBridge M (M.mate e) ↔ Degen.IsBridge M e := by
  have hr : Degen.AdjWithoutBond M (M.mate e) = Degen.AdjWithoutBond M e := by
    funext a b
    apply propext
    unfold Degen.AdjWithoutBond
    simp only [M.mate_mate]
    constructor <;> rintro ⟨x,hx,hy,h1,h2⟩ <;> exact ⟨x,hx,hy,h2,h1⟩
  unfold Degen.IsBridge
  rw [hr,M.mate_mate]
  exact ⟨fun h hp => h hp.symm,fun h hp => h hp.symm⟩

theorem exists_outgoing_bridge (M : Molecule V D) (h : ∃ e : D,Degen.IsBridge M e) :
    ∃ e : D,Degen.IsBridge M e ∧ M.out e = true := by
  obtain ⟨e,he⟩ := h
  cases ho : M.out e
  · exact ⟨M.mate e,(isBridge_mate_iff M e).mpr he,by rw [M.out_mate,ho]; rfl⟩
  · exact ⟨e,he,ho⟩

theorem eraseBond_bondsBetween_le (M : Molecule V D) (e : D) (a b : V) :
    (eraseBond M e).bondsBetween a b ≤ M.bondsBetween a b := by
  apply card_le_card_of_injOn (fun x => x.val)
  · intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,he⟩
  · intro x hx y hy he
    exact Subtype.ext he

theorem noTripleBonds_eraseBond (M : Molecule V D) (e : D) (h : AppbNoTripleBonds M) :
    AppbNoTripleBonds (eraseBond M e) := by
  intro a ha b hb hab
  exact (eraseBond_bondsBetween_le M e a b).trans (h a ha b hb hab)

end WaveTurbulence.Mole.AppbAlgorithm
