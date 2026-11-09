/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveSpine

/-!
# Derivation of the cell decomposition, XI: the pendant ports

For `k < s` the region `S ∖ H k` (everything but the pendant blocks `Y k, …`) is crossed by exactly two bonds, with
their inner ends at two distinct atoms of `Y k` (N3 Theorem 6 (iii): `H k` is joined to the rest by two single bonds
with distinct ends in `Y k`); for `k + 1 < s` these are the bonds `Y k – Y (k+1)` of the next level.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem crosses_compl {X : Finset V} (e : Bond M S) : Crosses (S \ X) e ↔ Crosses X e := by
  unfold Crosses
  have h1 := tl_mem e; have h2 := hd_mem e
  simp only [mem_sdiff, h1, h2, true_and, not_not]
  tauto

theorem portSet_compl {X : Finset V} : portSet (M := M) (S := S) (S \ X) = portSet X := by
  ext e; rw [mem_portSet, mem_portSet, crosses_compl]

theorem portSet_eq_cross {X : Finset V} : portSet (M := M) (S := S) X = cross X (S \ X) := by
  ext e
  rw [mem_portSet, mem_cross]
  unfold Crosses
  have h1 := tl_mem e; have h2 := hd_mem e
  simp only [mem_sdiff, h1, h2, true_and]
  tauto

/-- **Two single exits** give the two crossing bonds, with distinct inner ends in `Y`. -/
theorem exits_of {H Y : Finset V} {x x' : V} (hH : H ⊆ S) (hYH : Y ⊆ H) (h : TwoSingleExits M S H Y x x') :
    ∀ e ∈ portSet (M := M) (S := S) H, (tl e ∈ Y ∧ hd e ∉ H) ∨ (hd e ∈ Y ∧ tl e ∉ H) := by
  classical
  obtain ⟨hcard, hxx', hxS, hx'S, y, hy, y', hy', hyy', hb1, hb2⟩ := h
  have hxS' : x ∈ S := (mem_sdiff.mp hxS).1
  have hx'S' : x' ∈ S := (mem_sdiff.mp hx'S).1
  obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp ((card_cross_single (M := M) hxS' (hH (hYH hy))).trans hb1)
  obtain ⟨β', hβ'⟩ := Finset.card_eq_one.mp ((card_cross_single (M := M) hx'S' (hH (hYH hy'))).trans hb2)
  have hβm : β ∈ cross (M := M) (S := S) {x} {y} := by rw [hβ]; exact mem_singleton_self _
  have hβ'm : β' ∈ cross (M := M) (S := S) {x'} {y'} := by rw [hβ']; exact mem_singleton_self _
  rw [mem_cross] at hβm hβ'm
  simp only [mem_singleton] at hβm hβ'm
  have hxH : x ∉ H := (mem_sdiff.mp hxS).2
  have hx'H : x' ∉ H := (mem_sdiff.mp hx'S).2
  have hne : β ≠ β' := by
    intro h; subst h
    rcases hβm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hβ'm with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hxx' (h1.symm.trans h3)
    · exact hxH (by rw [← h1, h3]; exact hYH hy')
    · exact hxH (by rw [← h2, h4]; exact hYH hy')
    · exact hxx' (h2.symm.trans h4)
  have hsub : ({β, β'} : Finset (Bond M S)) ⊆ portSet H := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rw [mem_portSet]; unfold Crosses
    rcases he with rfl | rfl
    · rcases hβm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; rw [h1, h2]; exact ⟨hYH hy, hxH⟩
      · left; rw [h1, h2]; exact ⟨hYH hy, hxH⟩
    · rcases hβ'm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; rw [h1, h2]; exact ⟨hYH hy', hx'H⟩
      · left; rw [h1, h2]; exact ⟨hYH hy', hx'H⟩
  have hset : portSet (M := M) (S := S) H = {β, β'} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [portSet_eq_cross, card_cross hH sdiff_subset, hcard, card_pair hne]
  intro e he
  rw [hset, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · rcases hβm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, h2]; exact ⟨hy, hxH⟩
    · left; rw [h1, h2]; exact ⟨hy, hxH⟩
  · rcases hβ'm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, h2]; exact ⟨hy', hx'H⟩
    · left; rw [h1, h2]; exact ⟨hy', hx'H⟩

namespace Lay

variable (L : Lay M S a b) (hB : M.IsBlock S a b)
include hB

theorem card_pend {k : ℕ} (hk : k < L.s) : (portSet (M := M) (S := S) (S \ L.H k)).card = 2 := by
  obtain ⟨-, -, -, -, -, hex⟩ := L.pend_of hk
  obtain ⟨x, x', ⟨hcard, -⟩, -⟩ := hex k hk
  rw [portSet_compl, portSet_eq_cross, card_cross (L.H_sub hB k) sdiff_subset, hcard]

/-- The inner (pendant-side) ends of the crossing bonds of `S ∖ H k` lie in `Y k`. -/
theorem pend_inner {k : ℕ} (hk : k < L.s) (e : Bond M S) (he : e ∈ portSet (M := M) (S := S) (S \ L.H k)) :
    (tl e ∈ L.Y k ∧ hd e ∉ L.H k) ∨ (hd e ∈ L.Y k ∧ tl e ∉ L.H k) := by
  obtain ⟨-, -, -, -, -, hex⟩ := L.pend_of hk
  obtain ⟨x, x', h, -⟩ := hex k hk
  rw [portSet_compl] at he
  exact exits_of (L.H_sub hB k) (L.Y_sub_H hk) h e he

/-- The outer ends of the crossing bonds of `S ∖ H (k+1)` lie in `Y k`. -/
theorem pend_outer {k : ℕ} (hk : k + 1 < L.s) (e : Bond M S)
    (he : e ∈ portSet (M := M) (S := S) (S \ L.H (k + 1))) :
    (tl e ∈ L.Y k ∧ hd e ∈ L.H (k + 1)) ∨ (hd e ∈ L.Y k ∧ tl e ∈ L.H (k + 1)) := by
  rw [portSet_compl, portSet_eq_cross, L.cross_H_eq hB hk (by omega), mem_cross] at he
  simp only [show k + 1 - 1 = k by omega] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, L.Y_sub_H hk h2⟩
  · right; exact ⟨h2, L.Y_sub_H hk h1⟩

end Lay

end WaveTurbulence.TVine.Chart
