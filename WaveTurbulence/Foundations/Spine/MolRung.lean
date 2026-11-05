/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Ladders
import Mathlib.Tactic
/-! Interior rungs of a ladder: the four rail darts and the cancellation of the rung darts. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LadderDisjoint
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem mem_neighborDarts' (M : Molecule V D) (a b : V) (x : D) :
    x ∈ neighborDarts M a b ↔ M.atom x = a ∧ M.atom (M.mate x) = b := by
  unfold neighborDarts
  simp [Molecule.dartsAt]

omit [DecidableEq D] in
theorem sum_neighbor_mate (M : Molecule V D) {E : Type*} [AddCommGroup E] (a b : V) (g : D → E)
    (hg : ∀ x, g (M.mate x) = - g x) :
    ∑ y ∈ neighborDarts M b a, g y = - ∑ x ∈ neighborDarts M a b, g x := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun y => M.mate y) (fun x => M.mate x) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_neighborDarts'] at hy ⊢
    rw [M.mate_mate]; exact ⟨hy.2, hy.1⟩
  · intro x hx
    rw [mem_neighborDarts'] at hx ⊢
    rw [M.mate_mate]; exact ⟨hx.2, hx.1⟩
  · intro y _; exact M.mate_mate y
  · intro x _; exact M.mate_mate x
  · intro y _
    have := hg (M.mate y)
    rw [M.mate_mate] at this
    rw [this]

omit [DecidableEq D] in
theorem disjoint_neighborDarts (M : Molecule V D) (a : V) {x y : V} (hxy : x ≠ y) :
    Disjoint (neighborDarts M a x) (neighborDarts M a y) := by
  refine Finset.disjoint_left.mpr (fun z hz hw => hxy ?_)
  rw [mem_neighborDarts'] at hz hw
  exact hz.2.symm.trans hw.2

theorem dartsAt_interior (M : Molecule V D) {a b c e : V} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h2 : M.bondsBetween a b = 2) (h1 : M.bondsBetween a c = 1) (h3 : M.bondsBetween a e = 1)
    (hd : M.deg a ≤ 4) :
    M.dartsAt a = neighborDarts M a b ∪ neighborDarts M a c ∪ neighborDarts M a e := by
  have hsub : neighborDarts M a b ∪ neighborDarts M a c ∪ neighborDarts M a e ⊆ M.dartsAt a := by
    intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz <;> exact (Finset.mem_filter.mp hz).1
  have hdis1 := disjoint_neighborDarts M a hbc
  have hdis2 : Disjoint (neighborDarts M a b ∪ neighborDarts M a c) (neighborDarts M a e) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_neighborDarts M a hbe, disjoint_neighborDarts M a hce⟩
  have hcard : (neighborDarts M a b ∪ neighborDarts M a c ∪ neighborDarts M a e).card = 4 := by
    rw [Finset.card_union_of_disjoint hdis2, Finset.card_union_of_disjoint hdis1,
      card_neighborDarts M hab, card_neighborDarts M hac, card_neighborDarts M hae, h2, h1, h3]
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard]; exact hd

theorem sum_dartsAt_interior (M : Molecule V D) {E : Type*} [AddCommGroup E] {a b c e : V}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h2 : M.bondsBetween a b = 2) (h1 : M.bondsBetween a c = 1) (h3 : M.bondsBetween a e = 1)
    (hd : M.deg a ≤ 4) (g : D → E) :
    ∑ x ∈ M.dartsAt a, g x = ∑ x ∈ neighborDarts M a b, g x + ∑ x ∈ neighborDarts M a c, g x +
      ∑ x ∈ neighborDarts M a e, g x := by
  rw [dartsAt_interior M hab hac hae hbc hbe hce h2 h1 h3 hd]
  have hdis1 := disjoint_neighborDarts M a hbc
  have hdis2 : Disjoint (neighborDarts M a b ∪ neighborDarts M a c) (neighborDarts M a e) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_neighborDarts M a hbe, disjoint_neighborDarts M a hce⟩
  rw [Finset.sum_union hdis2, Finset.sum_union hdis1]

theorem rung_sum (M : Molecule V D) {a b la ra lb rb : V}
    (hab : a ≠ b) (hala : a ≠ la) (hara : a ≠ ra) (hbla : b ≠ la) (hbra : b ≠ ra) (hlara : la ≠ ra)
    (hbalb : b ≠ lb) (hbrb : b ≠ rb) (haab : a ≠ lb) (haarb : a ≠ rb) (hlbrb : lb ≠ rb)
    (h2 : M.bondsBetween a b = 2) (hla : M.bondsBetween a la = 1) (hra : M.bondsBetween a ra = 1)
    (hlb : M.bondsBetween b lb = 1) (hrb : M.bondsBetween b rb = 1)
    (hda : M.deg a ≤ 4) (hdb : M.deg b ≤ 4) :
    ∃ pL pR qL qR : D, neighborDarts M a la = {pL} ∧ neighborDarts M a ra = {pR} ∧
      neighborDarts M b lb = {qL} ∧ neighborDarts M b rb = {qR} ∧
      ∀ {E : Type} [AddCommGroup E] (g : D → E), (∀ x, g (M.mate x) = - g x) →
        ∑ x ∈ M.dartsAt a, g x + ∑ x ∈ M.dartsAt b, g x = g pL + g pR + g qL + g qR := by
  have c1 := card_neighborDarts M hala
  have c2 := card_neighborDarts M hara
  have c3 := card_neighborDarts M hbalb
  have c4 := card_neighborDarts M hbrb
  rw [hla] at c1; rw [hra] at c2; rw [hlb] at c3; rw [hrb] at c4
  obtain ⟨pL, hpL⟩ := Finset.card_eq_one.mp c1
  obtain ⟨pR, hpR⟩ := Finset.card_eq_one.mp c2
  obtain ⟨qL, hqL⟩ := Finset.card_eq_one.mp c3
  obtain ⟨qR, hqR⟩ := Finset.card_eq_one.mp c4
  refine ⟨pL, pR, qL, qR, hpL, hpR, hqL, hqR, ?_⟩
  intro E _ g hg
  rw [sum_dartsAt_interior M hab hala hara hbla.symm.symm hbra hlara h2 hla hra hda g]
  rw [sum_dartsAt_interior M hab.symm hbalb hbrb haab.symm.symm haarb hlbrb
    (by rw [LadderDisjoint.bondsBetween_comm]; exact h2) hlb hrb hdb g]
  rw [hpL, hpR, hqL, hqR]
  have hs := sum_neighbor_mate M a b g hg
  simp only [Finset.sum_singleton]
  rw [hs]
  abel

end WaveTurbulence.Ladder
