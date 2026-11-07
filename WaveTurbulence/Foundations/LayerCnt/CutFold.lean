/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutRung
import Mathlib.Tactic

/-! # Cut labellings extend through all later insertions (TARGET layervine, L1531)

Bookkeeping for the fold `xs.foldl insertRungs T`: atoms stay bounded, the counts of the (distinct) slot bonds
do not increase, and a cut labelling whose slot endpoints lie on one outer side extends through every later slot.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

theorem railBonds_bound {a b k N : ℕ} {g : ℕ → ℕ} (ha : a < N) (hb : b < N) (hg : ∀ j < k, g j < N)
    {e : ℕ × ℕ} (he : e ∈ railBonds a ((List.range k).map g) b) : e.1 < N ∧ e.2 < N := by
  obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
  have : ∀ m, m ≤ k + 1 → railSeq a b k g m < N := by
    intro m hm
    unfold railSeq
    split_ifs
    · exact ha
    · exact hg _ (by omega)
    · exact hb
  exact ⟨this m (by omega), this (m + 1) (by omega)⟩

theorem railBonds_has_new {a b k n : ℕ} {g : ℕ → ℕ} (hk : k ≠ 0) (hg : ∀ j < k, n ≤ g j)
    {e : ℕ × ℕ} (he : e ∈ railBonds a ((List.range k).map g) b) : n ≤ e.1 ∨ n ≤ e.2 := by
  obtain ⟨m, hm, rfl⟩ := mem_railBonds_range he
  by_cases h0 : m = 0
  · subst h0; right; simp only [railSeq]; rw [if_neg (by omega), if_pos (by omega)]; exact hg _ (by omega)
  · left; simp only [railSeq]; rw [if_neg h0, if_pos (by omega)]; exact hg _ (by omega)

theorem bdd_insert {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ}
    (hends : ∀ v ∈ slotEnds s, v < T.n) (hbdd : ∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) :
    ∀ e ∈ (insertRungs T s k).bonds, e.1 < (insertRungs T s k).n ∧ e.2 < (insertRungs T s k).n := by
  intro e he
  rw [insertRungs_atoms]
  by_cases hk : k = 0
  · subst hk; rw [insertRungs_zero] at he; have := hbdd e he; omega
  simp only [insertRungs, hk, ite_false, List.mem_append] at he
  have hxn : s.1.1 < T.n := hends _ (by simp [slotEnds])
  have hyn : s.1.2 < T.n := hends _ (by simp [slotEnds])
  have hxn' : s.2.1 < T.n := hends _ (by simp [slotEnds])
  have hyn' : s.2.2 < T.n := hends _ (by simp [slotEnds])
  rcases he with ((he | he) | he) | he
  · have := hbdd e (List.mem_of_mem_erase (List.mem_of_mem_erase he)); omega
  · have := railBonds_bound (N := T.n + 2 * k) (g := fun j => T.n + j) (by omega) (by omega)
      (fun j hj => by omega) he
    exact this
  · have := railBonds_bound (N := T.n + 2 * k) (g := fun j => T.n + k + j) (by omega) (by omega)
      (fun j hj => by omega) he
    exact this
  · rw [List.mem_flatMap] at he
    obtain ⟨p, hp, hep⟩ := he
    have hep' : e = p := by simpa using hep
    subst hep'
    rw [List.zip_map'] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := List.mem_range.mp hi
    simp only; omega

theorem count_insert_le {T : VineTemplate} {s : (ℕ × ℕ) × (ℕ × ℕ)} {k : ℕ} {e : ℕ × ℕ}
    (he : e.1 < T.n ∧ e.2 < T.n) :
    (insertRungs T s k).bonds.count e ≤ T.bonds.count e := by
  by_cases hk : k = 0
  · subst hk; rw [insertRungs_zero]
  simp only [insertRungs, hk, ite_false, List.count_append]
  have h1 : (railBonds s.1.1 ((List.range k).map (T.n + ·)) s.1.2).count e = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    have := railBonds_has_new (n := T.n) hk (fun j hj => by show T.n ≤ T.n + j; omega) hm
    omega
  have h2 : (railBonds s.2.1 ((List.range k).map (T.n + k + ·)) s.2.2).count e = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    have := railBonds_has_new (n := T.n) hk (fun j hj => by show T.n ≤ T.n + k + j; omega) hm
    omega
  have h3 : ((List.zip ((List.range k).map (T.n + ·)) ((List.range k).map (T.n + k + ·))).flatMap
      (fun p => [p, p])).count e = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    rw [List.mem_flatMap] at hm
    obtain ⟨p, hp, hep⟩ := hm
    have hep' : e = p := by simpa using hep
    subst hep'
    rw [List.zip_map'] at hp
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hp
    subst hie
    simp only at he; omega
  rw [h1, h2, h3]
  simpa using (List.erase_sublist.trans List.erase_sublist |>.count_le e |>.trans' (le_refl _) : _)

end WaveTurbulence.LayerCnt
