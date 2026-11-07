/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # DH23 Appendix B: deleting one actual bond

Both darts are removed, while the vertices remain, including newly isolated
ones. The degree identity counts loops twice and applies to bridge removal.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact retained incidence enumeration for deletion of a bond. -/
theorem appb_eraseBond_degree_card (M : Molecule V D) (e : D) (v : V) :
    (eraseBond M e).deg v = ((M.dartsAt v).filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have ha : M.atom x.val = v := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨by simp only [Molecule.dartsAt,mem_filter,mem_univ,true_and]; exact ha, x.property⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hx,hp⟩ := mem_filter.mp hx
    refine ⟨⟨x,hp⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩

/-- A bond deletion lowers each endpoint degree by one. For a loop it
lowers its single endpoint degree by two. -/
theorem appb_eraseBond_degree (M : Molecule V D) (e : D) (v : V) :
    (eraseBond M e).deg v + (if M.atom e = v then 1 else 0) +
      (if M.atom (M.mate e) = v then 1 else 0) = M.deg v := by
  rw [appb_eraseBond_degree_card]
  have hne : e ≠ M.mate e := (M.mate_ne e).symm
  have hs : (M.dartsAt v).filter (fun x => x ≠ e ∧ x ≠ M.mate e) =
      M.dartsAt v \ {e,M.mate e} := by
    ext x
    simp only [mem_filter,mem_sdiff,mem_insert,mem_singleton,not_or]
  rw [hs]
  have hc := card_sdiff_add_card_inter (M.dartsAt v) {e,M.mate e}
  have hi : ((M.dartsAt v) ∩ {e,M.mate e}).card =
      (if M.atom e = v then 1 else 0) + (if M.atom (M.mate e) = v then 1 else 0) := by
    rw [inter_comm]
    by_cases ha : M.atom e = v <;> by_cases hb : M.atom (M.mate e) = v
    all_goals simp [Molecule.dartsAt,ha,hb,hne]
  rw [hi] at hc
  exact (Nat.add_assoc _ _ _).trans hc

/-- Every bond deletion removes exactly one outgoing representative. -/
theorem appb_eraseBond_card_bonds (M : Molecule V D) (e : D) :
    (eraseBond M e).bonds.card + 1 = M.bonds.card := by
  have hmap : (eraseBond M e).bonds.card =
      (M.bonds.filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
    apply card_bij (fun x _ => x.val)
    · intro x hx
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,x.property⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro x hx
      obtain ⟨hx,hp⟩ := mem_filter.mp hx
      exact ⟨⟨x,hp⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,rfl⟩
  rw [hmap]
  have hc := card_filter_add_card_filter_not (s := M.bonds) (fun x => x = e ∨ x = M.mate e)
  have hf : (M.bonds.filter fun x => x = e ∨ x = M.mate e).card = 1 := by
    cases ho : M.out e
    · have he : M.out (M.mate e) = true := by rw [M.out_mate,ho]; rfl
      have hh : M.bonds.filter (fun x => x = e ∨ x = M.mate e) = {M.mate e} := by
        ext x
        simp only [mem_filter,Molecule.bonds,mem_univ,true_and,mem_singleton]
        constructor
        · rintro ⟨hx,rfl|hx⟩
          · simp [ho] at hx
          · exact hx
        · rintro rfl
          exact ⟨he,Or.inr rfl⟩
      rw [hh,card_singleton]
    · have he : M.out (M.mate e) = false := by rw [M.out_mate,ho]; rfl
      have hh : M.bonds.filter (fun x => x = e ∨ x = M.mate e) = {e} := by
        ext x
        simp only [mem_filter,Molecule.bonds,mem_univ,true_and,mem_singleton]
        constructor
        · rintro ⟨hx,hx|rfl⟩
          · exact hx
          · simp [he] at hx
        · rintro rfl
          exact ⟨ho,Or.inl rfl⟩
      rw [hh,card_singleton]
  have hn : M.bonds.filter (fun x => ¬(x = e ∨ x = M.mate e)) =
      M.bonds.filter (fun x => x ≠ e ∧ x ≠ M.mate e) := by
    ext x
    simp only [mem_filter,not_or]
  rw [hf,hn] at hc
  omega

end WaveTurbulence.Mole
