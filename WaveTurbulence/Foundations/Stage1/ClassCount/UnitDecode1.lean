/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitFamily
import Mathlib.Tactic

/-!
# CLASSCOUNT: orientations of an unordered bond list

If a multiset `P` of ordered pairs has the same unordered pairs as a list `L`, then `P` is the multiset of the
pairs of `L` oriented by a list of booleans (`exists_orientation`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

/-- The pair of a bond list entry, oriented by a boolean. -/
def orient (q : (ℕ × ℕ) × Bool) : ℕ × ℕ := if q.2 then q.1 else (q.1.2, q.1.1)

theorem exists_orientation (L : List (ℕ × ℕ)) :
    ∀ (P : Multiset (ℕ × ℕ)),
      P.map (fun p => s(p.1, p.2)) = (L.map (fun p => s(p.1, p.2)) : Multiset (Sym2 ℕ)) →
      ∃ o : List Bool, o.length = L.length ∧ (((L.zip o).map orient : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) = P := by
  induction L with
  | nil =>
    intro P h
    simp only [List.map_nil, Multiset.coe_nil, Multiset.map_eq_zero] at h
    exact ⟨[], rfl, by simp [h]⟩
  | cons l L ih =>
    intro P h
    simp only [List.map_cons, ← Multiset.cons_coe] at h
    have hmem : s(l.1, l.2) ∈ P.map (fun p => s(p.1, p.2)) := by rw [h]; simp
    obtain ⟨p, hp, hpl⟩ := Multiset.mem_map.mp hmem
    obtain ⟨P', rfl⟩ := Multiset.exists_cons_of_mem hp
    rw [Multiset.map_cons, hpl] at h
    have h' := Multiset.cons_inj_right _ |>.mp h
    obtain ⟨o, ho, hP⟩ := ih P' h'
    have hs : p = l ∨ p = (l.2, l.1) := by
      have := Sym2.eq_iff.mp hpl
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2
    rcases hs with rfl | rfl
    · refine ⟨true :: o, by simp [ho], ?_⟩
      simp only [List.zip_cons_cons, List.map_cons, ← Multiset.cons_coe, hP, orient, if_true]
    · refine ⟨false :: o, by simp [ho], ?_⟩
      simp only [List.zip_cons_cons, List.map_cons, ← Multiset.cons_coe, hP, orient, Bool.false_eq_true,
        if_false]

end WaveTurbulence.ClassCount
