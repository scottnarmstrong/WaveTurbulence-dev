/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Base
import Mathlib.Tactic

/-! # G8-XROUTE: the terminal molecules `X` and the quadrilateral of double bonds

`IsX` is DH23's crossed molecule (`a=b`, `c=d`, `ac`, `ad`, `bc`, `bd`).  `IsQuad` is the quadrilateral of four
double bonds; it is the only other 4-regular loop-free connected molecule on four atoms without a triple bond, and
it occurs as `𝕄₁` itself (route length `0`).  `IsXFinal` is their disjunction; both are core molecules without a
two-dart cut in which every atom has a double partner, which is exactly what `afree_case_pair` consumes.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The crossed molecule `X`** (case-4 note, F6-2). -/
def IsX (M : Molecule V D) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ M.atoms = {a, b, c, d} ∧
    M.bondsBetween a b = 2 ∧ M.bondsBetween c d = 2 ∧ M.bondsBetween a c = 1 ∧ M.bondsBetween a d = 1 ∧
    M.bondsBetween b c = 1 ∧ M.bondsBetween b d = 1

/-- **The quadrilateral of double bonds.** -/
def IsQuad (M : Molecule V D) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ M.atoms = {a, b, c, d} ∧
    M.bondsBetween a b = 2 ∧ M.bondsBetween b c = 2 ∧ M.bondsBetween c d = 2 ∧ M.bondsBetween d a = 2 ∧
    M.bondsBetween a c = 0 ∧ M.bondsBetween b d = 0

/-- The terminal molecules of an `X`-route. -/
def IsXFinal (M : Molecule V D) : Prop := IsX M ∨ IsQuad M

theorem bb_zero_of_notMem' (M : Molecule V D) {p : V} (hp : p ∉ M.atoms) (q : V) : M.bondsBetween p q = 0 := by
  by_contra h
  exact hp (mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega))

theorem IsXFinal.facts {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (h : IsXFinal M) :
    M.atoms.card = 4 ∧ (∀ p q, M.bondsBetween p q ≤ 2) ∧ (∀ p ∈ M.atoms, ∃ w, M.bondsBetween p w = 2) := by
  have sym := bondsBetween_symm M
  have hself := bondsBetween_self_eq_zero hloop
  have key : ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → M.atoms = {a, b, c, d} →
      (∃ w, M.bondsBetween a w = 2) → (∃ w, M.bondsBetween b w = 2) → (∃ w, M.bondsBetween c w = 2) →
      (∃ w, M.bondsBetween d w = 2) →
      (∀ p ∈ ({a, b, c, d} : Finset V), ∀ q ∈ ({a, b, c, d} : Finset V), M.bondsBetween p q ≤ 2) →
      M.atoms.card = 4 ∧ (∀ p q, M.bondsBetween p q ≤ 2) ∧ (∀ p ∈ M.atoms, ∃ w, M.bondsBetween p w = 2) := by
    intro a b c d hab hac had hbc hbd hcd hs ha hb hc hd hle
    refine ⟨?_, fun p q => ?_, fun p hp => ?_⟩
    · rw [hs]; simp [hab, hac, had, hbc, hbd, hcd]
    · by_cases hp : p ∈ M.atoms
      · by_cases hq : q ∈ M.atoms
        · rw [hs] at hp hq; exact hle p hp q hq
        · rw [sym]; rw [bb_zero_of_notMem' M hq]; omega
      · rw [bb_zero_of_notMem' M hp]; omega
    · rw [hs] at hp
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
  rcases h with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, h1, h2, h3, h4, h5, h6⟩ |
      ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, h1, h2, h3, h4, h5, h6⟩
  · refine key a b c d hab hac had hbc hbd hcd hs ⟨b, h1⟩ ⟨a, by rw [sym]; exact h1⟩ ⟨d, h2⟩
      ⟨c, by rw [sym]; exact h2⟩ ?_
    intro p hp q hq
    simp only [mem_insert, mem_singleton] at hp hq
    have := hself a; have := hself b; have := hself c; have := hself d
    have := sym b a; have := sym c a; have := sym d a; have := sym c b; have := sym d b; have := sym d c
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> omega
  · refine key a b c d hab hac had hbc hbd hcd hs ⟨b, h1⟩ ⟨c, h2⟩ ⟨d, h3⟩ ⟨a, h4⟩ ?_
    intro p hp q hq
    simp only [mem_insert, mem_singleton] at hp hq
    have := hself a; have := hself b; have := hself c; have := hself d
    have := sym b a; have := sym c a; have := sym d a; have := sym c b; have := sym d b; have := sym d c
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> omega

/-- A loop-free regular molecule on four atoms has no cut of exactly two darts when all bond counts are `≤ 2`. -/
theorem no_two_cross_of_four {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hreg : ∀ a ∈ M.atoms, M.deg a = 4) (hc4 : M.atoms.card = 4) (hle : ∀ p q, M.bondsBetween p q ≤ 2) :
    ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2 := by
  intro S hS a ha b hb hbS
  have h1 : 1 ≤ S.card := card_pos.mpr ⟨a, ha⟩
  have h3 : S.card < 4 := by
    rw [← hc4]; exact card_lt_card ⟨hS, fun h => hbS (h hb)⟩
  have hn : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hn with hn | hn | hn
  · obtain ⟨u, rfl⟩ := card_eq_one.mp hn
    rw [card_cross_singleton M hloop, hreg u (hS (mem_singleton_self u))]; norm_num
  · obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hn
    have hp : p ∈ M.atoms := hS (by simp)
    have hq : q ∈ M.atoms := hS (by simp)
    have := card_cross_pair M hloop hpq
    rw [hreg p hp, hreg q hq] at this
    have := hle p q
    omega
  · have hc : (M.atoms \ S).card = 1 := by rw [card_sdiff_of_subset hS, hc4, hn]
    obtain ⟨u, hu⟩ := card_eq_one.mp hc
    have hSe : S = M.atoms \ (M.atoms \ S) := by
      rw [sdiff_sdiff_right_self, inf_eq_right.mpr hS]
    have hmem : u ∈ M.atoms := by
      have : u ∈ M.atoms \ S := by rw [hu]; exact mem_singleton_self u
      exact (mem_sdiff.mp this).1
    rw [hSe, card_crossDarts_compl, hu, card_cross_singleton M hloop, hreg u hmem]; norm_num

theorem IsXFinal.isCore {M : Molecule V D} (h : IsXFinal M) (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hreg : ∀ a ∈ M.atoms, M.deg a = 4)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) : IsCore M := by
  obtain ⟨hc4, hle, _⟩ := h.facts hloop
  refine ⟨hcap, hloop, hreg, hconn, hle, ?_⟩
  rintro ⟨e, f, g, _, _, _, hs, _⟩
  have := card_le_three (a := e) (b := f) (c := g)
  rw [← hs, hc4] at this
  omega

theorem IsXFinal.noTwoCross {M : Molecule V D} (h : IsXFinal M) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hreg : ∀ a ∈ M.atoms, M.deg a = 4) :
    ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2 :=
  let hf := h.facts hloop
  no_two_cross_of_four hloop hreg hf.1 hf.2.1

theorem IsXFinal.double {M : Molecule V D} (h : IsXFinal M) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (e : D) :
    ∃ w, M.bondsBetween (M.atom e) w = 2 ∨ M.bondsBetween (M.atom (M.mate e)) w = 2 := by
  obtain ⟨w, hw⟩ := (h.facts hloop).2.2 _ (M.atom_mem e)
  exact ⟨w, Or.inl hw⟩

end WaveTurbulence.FinalCountG8
