/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DerivePorts

/-!
# Derivation of the cell decomposition, IX: the attachment bonds and the spine ports

* With a pendant, `H 0` is joined to the rest by exactly two single bonds `α` (at the outer end `x`) and `α'` (at
  `x'`), whose inner ends are in the pendant top `Y 0` (N3 Theorem 6 (iii)).
* `Att`: no pendant, (P-a) at the junction `Z j`, or (P-b) at the step `j` (`Z j – Z (j+1)` single).
* The spine regions: the exit region of `Z i` is `reg i (hx i)` and the entry region of `Z (i+1)` is
  `reg i (he i)`; they coincide except at the (P-b) step.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem card_cross_single {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (cross (M := M) (S := S) {x} {y}).card = M.bondsBetween x y := by
  classical
  rw [card_cross (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy)]
  unfold crossBonds Molecule.bondsBetween
  congr 1
  apply Finset.filter_congr
  intro z _
  simp only [mem_singleton, Molecule.ends, Sym2.eq_iff]
  try tauto

/-- The pendant attachment. -/
inductive Att
  | none
  | pa (j : ℕ)
  | pb (j : ℕ)
  deriving DecidableEq

/-- The pendant flag of the exit region of `Z i`. -/
def Att.hx : Att → ℕ → Bool
  | .none, _ => false
  | .pa j, i => decide (j ≤ i)
  | .pb j, i => decide (j < i)

/-- The pendant flag of the entry region of `Z (i+1)`. -/
def Att.he : Att → ℕ → Bool
  | .none, _ => false
  | .pa j, i => decide (j ≤ i)
  | .pb j, i => decide (j ≤ i)

namespace Lay

variable (L : Lay M S a b) (hB : M.IsBlock S a b)

/-- **The attachment data.** -/
structure AttData (L : Lay M S a b) (att : Att) where
  α : Bond M S
  α' : Bond M S
  x : V
  x' : V
  y : V
  y' : V
  /-- the attachment bonds, when there is a pendant -/
  pend : 1 ≤ L.s → α ≠ α' ∧ cross (L.H 0) (S \ L.H 0) = {α, α'} ∧ x ≠ x' ∧ y ≠ y' ∧ y ∈ L.Y 0 ∧ y' ∈ L.Y 0 ∧
    ((tl α = x ∧ hd α = y) ∨ (tl α = y ∧ hd α = x)) ∧ ((tl α' = x' ∧ hd α' = y') ∨ (tl α' = y' ∧ hd α' = x'))
  case : match att with
    | .none => L.s = 0 ∧ ∃ i, 1 ≤ i ∧ i ≤ L.r ∧ IsCoreBC M (L.Z i)
    | .pa j => 1 ≤ L.s ∧ 1 ≤ j ∧ j ≤ L.r ∧ x ∈ L.Z j ∧ x' ∈ L.Z j ∧ IsJunctionPiece M (L.Z j)
    | .pb j => 1 ≤ L.s ∧ j ≤ L.r ∧ crossBonds M (L.Z j) (L.Z (j + 1)) = 1 ∧ x ∈ L.Z j ∧ x' ∈ L.Z (j + 1)

include hB in
/-- **The attachment exists.** -/
theorem att_exists : ∃ att : Att, Nonempty (L.AttData att) := by
  classical
  rcases L.pend with ⟨hs0, hBC⟩ | ⟨hs1, -, -, -, -, hex⟩
  · have hc : (univ.filter fun e : Bond M S => tl e = b).card = 1 := by
      rw [card_tl]; exact hB.2.2.2.2.2.2.1
    obtain ⟨e, -⟩ := Finset.card_pos.mp (by omega : 0 < (univ.filter fun e : Bond M S => tl e = b).card)
    exact ⟨.none, ⟨⟨e, e, a, a, a, a, fun h => absurd h (by omega), ⟨hs0, hBC⟩⟩⟩⟩
  obtain ⟨x, x', ⟨hcard, hxx', hxS, hx'S, y, hy, y', hy', hyy', hb1, hb2⟩, hatt⟩ := hex 0 (by omega)
  have hxS' : x ∈ S := (mem_sdiff.mp hxS).1
  have hx'S' : x' ∈ S := (mem_sdiff.mp hx'S).1
  have hyS : y ∈ S := L.Y_sub hB (by omega) hy
  have hy'S : y' ∈ S := L.Y_sub hB (by omega) hy'
  obtain ⟨α, hα⟩ := Finset.card_eq_one.mp ((card_cross_single (M := M) hxS' hyS).trans hb1)
  obtain ⟨α', hα'⟩ := Finset.card_eq_one.mp ((card_cross_single (M := M) hx'S' hy'S).trans hb2)
  have hαm : α ∈ cross (M := M) (S := S) {x} {y} := by rw [hα]; exact mem_singleton_self _
  have hα'm : α' ∈ cross (M := M) (S := S) {x'} {y'} := by rw [hα']; exact mem_singleton_self _
  rw [mem_cross] at hαm hα'm
  simp only [mem_singleton] at hαm hα'm
  have hxH : x ∉ L.H 0 := (mem_sdiff.mp hxS).2
  have hx'H : x' ∉ L.H 0 := (mem_sdiff.mp hx'S).2
  have hyH : y ∈ L.H 0 := L.Y_sub_H (by omega) hy
  have hy'H : y' ∈ L.H 0 := L.Y_sub_H (by omega) hy'
  have hne : α ≠ α' := by
    intro h; subst h
    rcases hαm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hα'm with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hxx' (h1.symm.trans h3)
    · exact hxH (by rw [← h1, h3]; exact hy'H)
    · exact hxH (by rw [← h2, h4]; exact hy'H)
    · exact hxx' (h2.symm.trans h4)
  have hset : cross (M := M) (S := S) (L.H 0) (S \ L.H 0) = {α, α'} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [mem_insert, mem_singleton] at he
      rw [mem_cross]
      rcases he with rfl | rfl
      · rcases hαm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; rw [h1, h2]; exact ⟨hxS, hyH⟩
        · left; rw [h1, h2]; exact ⟨hyH, hxS⟩
      · rcases hα'm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; rw [h1, h2]; exact ⟨hx'S, hy'H⟩
        · left; rw [h1, h2]; exact ⟨hy'H, hx'S⟩
    · rw [card_cross (L.H_sub hB 0) sdiff_subset, hcard, card_pair hne]
  have hpend : 1 ≤ L.s → α ≠ α' ∧ cross (M := M) (S := S) (L.H 0) (S \ L.H 0) = {α, α'} ∧ x ≠ x' ∧ y ≠ y' ∧
      y ∈ L.Y 0 ∧ y' ∈ L.Y 0 ∧ ((tl α = x ∧ hd α = y) ∨ (tl α = y ∧ hd α = x)) ∧
      ((tl α' = x' ∧ hd α' = y') ∨ (tl α' = y' ∧ hd α' = x')) := fun _ =>
    ⟨hne, hset, hxx', hyy', hy, hy', by tauto, by tauto⟩
  rcases hatt rfl with ⟨j, h1, h2, h3, h4, h5, -⟩ | ⟨j, h1, h2, h3⟩
  · exact ⟨.pa j, ⟨⟨α, α', x, x', y, y', hpend, ⟨hs1, h1, h2, h3, h4, h5⟩⟩⟩⟩
  · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact ⟨.pb j, ⟨⟨α, α', x, x', y, y', hpend, ⟨hs1, h1, h2, h3, h4⟩⟩⟩⟩
    · exact ⟨.pb j, ⟨⟨α', α, x', x, y', y, fun hs => ⟨hne.symm, by rw [hset, pair_comm], hxx'.symm,
        hyy'.symm, hy', hy, by tauto, by tauto⟩, ⟨hs1, h1, h2, h3, h4⟩⟩⟩⟩

end Lay

end WaveTurbulence.TVine.Chart
