/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreGraph
import Mathlib.Tactic

/-! # The core class and the merged molecule

`IsCore`: the molecules handled by the case analysis of Prop 10.4(2)′ (DH23 L1963: after the (Y) sequences): in/out
caps, no loops, 4-regular, connected, no triple bond, not the triangle `T`. Bond counts of the merged molecule, and the
facts that keep it in the core class (DH23 L1977: "M″ has no quadruple bond … and no triple bond").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The core class** of Prop 10.4(2)′. -/
structure IsCore (M : Molecule V D) : Prop where
  cap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2
  loop : ∀ z, M.atom z ≠ M.atom (M.mate z)
  reg : ∀ a ∈ M.atoms, M.deg a = 4
  conn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  le2 : ∀ p q, M.bondsBetween p q ≤ 2
  notT : ¬ IsT M

/-- The darts from `a` to `b ≠ a` are the bonds between them. -/
theorem card_darts_between (M : Molecule V D) {a b : V} (hab : a ≠ b) :
    (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b).card = M.bondsBetween a b := by
  classical
  have hb := Merge.pair_bonds_card (M := M) hab
  have hi1 := Merge.pair_in_card (M := M) a b
  have hs : (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b).card =
      (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b ∧ M.out x = true).card +
        (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b ∧ M.out x = false).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext x; simp only [mem_filter, mem_univ, true_and, mem_union]
      cases M.out x <;> simp
    · rw [disjoint_filter]; rintro x _ ⟨_, _, h⟩ ⟨_, _, h'⟩; rw [h] at h'; exact Bool.noConfusion h'
  omega

/-- **Degree as a sum of bond counts** (no loops): darts at `u` with the other end in `S`. -/
theorem card_darts_to_eq_sum (M : Molecule V D) {u : V} (S : Finset V) (hu : u ∉ S) :
    (univ.filter fun x => M.atom x = u ∧ M.atom (M.mate x) ∈ S).card = ∑ w ∈ S, M.bondsBetween u w := by
  classical
  rw [card_eq_sum_card_fiberwise (s := univ.filter fun x => M.atom x = u ∧ M.atom (M.mate x) ∈ S) (t := S)
    (f := fun x => M.atom (M.mate x)) (fun x hx => (mem_filter.mp hx).2.2)]
  refine sum_congr rfl fun w hw => ?_
  rw [← card_darts_between M (fun h => hu (by rw [h]; exact hw))]
  congr 1; ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hw⟩, h2⟩

omit [DecidableEq D] in
theorem deg_eq_card_darts (M : Molecule V D) (u : V) : M.deg u = (univ.filter fun x => M.atom x = u).card := rfl

/-- **Crossing darts by bond counts**: for `S ⊆ atoms` (no loops), `|∂S| = ∑_{u ∈ S} (deg u − ∑_{w ∈ S, w ≠ u} bb(u,w))`. -/
theorem card_cross_add_sum (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (S : Finset V) :
    (crossDarts M S).card + ∑ u ∈ S, ∑ w ∈ S.erase u, M.bondsBetween u w = ∑ u ∈ S, M.deg u := by
  classical
  rw [card_eq_sum_card_fiberwise (s := crossDarts M S) (t := S) (f := M.atom)
    (fun x hx => (mem_crossDarts.mp hx).1), ← sum_add_distrib]
  refine sum_congr rfl fun u hu => ?_
  rw [← card_darts_to_eq_sum M (S.erase u) (notMem_erase u S), deg_eq_card_darts, ← card_union_of_disjoint]
  · congr 1; ext x
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_crossDarts, mem_erase]
    constructor
    · rintro (⟨⟨_, h2⟩, h1⟩ | ⟨h1, _, _⟩) <;> exact h1
    · intro h1
      by_cases h : M.atom (M.mate x) ∈ S
      · exact Or.inr ⟨h1, fun h' => hloop x (h1.trans h'.symm), h⟩
      · exact Or.inl ⟨⟨h1 ▸ hu, h⟩, h1⟩
  · rw [disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_univ, true_and, mem_crossDarts, mem_erase] at h1 h2
    exact h1.1.2 h2.2.2

/-- **Degree as a sum of bond counts** (no loops). -/
theorem deg_eq_sum_bb (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (u : V) :
    M.deg u = ∑ w ∈ M.atoms.erase u, M.bondsBetween u w := by
  have h := card_cross_add_sum M hloop {u}
  have h0 : crossDarts M {u} = ∅ ∨ True := Or.inr trivial
  clear h0
  rw [card_cross_singleton M hloop u, sum_singleton, sum_singleton, erase_singleton, sum_empty] at h
  have h2 := card_darts_to_eq_sum M (M.atoms.erase u) (notMem_erase u M.atoms)
  rw [← h2, deg_eq_card_darts]
  congr 1; ext x
  simp only [mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · intro h1; exact ⟨h1, fun h' => hloop x (h1.trans h'.symm), M.atom_mem _⟩
  · exact fun h => h.1

omit [DecidableEq D] in
theorem bondsBetween_symm (M : Molecule V D) (a b : V) : M.bondsBetween a b = M.bondsBetween b a :=
  Degen.bondsBetween_comm M a b

namespace IsCore
variable {M : Molecule V D} (hM : IsCore M)
include hM

omit [DecidableEq D] in
/-- In a core molecule every atom has two outgoing and two incoming bonds. -/
theorem out_eq (a : V) (ha : a ∈ M.atoms) : M.outdeg a = 2 ∧ M.indeg a = 2 := by
  have h := Mole.outdeg_add_indeg M a
  have := hM.reg a ha
  have := hM.cap a ha
  omega

/-- A core molecule with an atom has at least four atoms. -/
theorem four_le_card {p : V} (hp : p ∈ M.atoms) : 4 ≤ M.atoms.card := by
  classical
  by_contra hlt
  push Not at hlt
  have hdeg := fun u (hu : u ∈ M.atoms) => (hM.reg u hu).symm.trans (deg_eq_sum_bb M hM.loop u)
  interval_cases h : M.atoms.card
  · exact absurd (card_pos.mpr ⟨p, hp⟩) (by omega)
  · obtain ⟨a, ha⟩ := card_eq_one.mp h
    have hpa : p = a := by rw [ha] at hp; exact mem_singleton.mp hp
    have he : M.atoms.erase p = ∅ := by rw [ha, hpa, erase_singleton]
    have := hdeg p hp
    rw [he, sum_empty] at this
    omega
  · obtain ⟨a, b, hab, hs⟩ := card_eq_two.mp h
    have ha : a ∈ M.atoms := by rw [hs]; simp
    have := hdeg a ha
    rw [hs, erase_insert_eq_erase, erase_eq_of_notMem (by simpa using hab), sum_singleton] at this
    have := hM.le2 a b
    omega
  · obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := card_eq_three.mp h
    have ha : a ∈ M.atoms := by rw [hs]; simp
    have hb : b ∈ M.atoms := by rw [hs]; simp
    have hc : c ∈ M.atoms := by rw [hs]; simp
    have e1 := hdeg a ha
    have e2 := hdeg b hb
    have e3 := hdeg c hc
    have s1 : M.atoms.erase a = {b, c} := by
      rw [hs]; ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
    have s2 : M.atoms.erase b = {a, c} := by
      rw [hs]; ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
    have s3 : M.atoms.erase c = {a, b} := by
      rw [hs]; ext x; simp only [mem_erase, mem_insert, mem_singleton]; aesop
    rw [s1, sum_pair hbc] at e1
    rw [s2, sum_pair hac] at e2
    rw [s3, sum_pair hab] at e3
    have l1 := hM.le2 a b; have l2 := hM.le2 a c; have l3 := hM.le2 b c
    rw [bondsBetween_symm M b a] at e2
    rw [bondsBetween_symm M c a, bondsBetween_symm M c b] at e3
    apply hM.notT
    refine ⟨a, b, c, hab, hbc, hac, hs, by omega, by omega, by omega, ?_⟩
    have hsum := Mole.sum_degrees_eq_two_mul_bonds M
    rw [sum_congr rfl hM.reg, sum_const, smul_eq_mul, h] at hsum
    omega

end IsCore

/-! ## Bond counts of the merged molecule -/

namespace Merge
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

omit [DecidableEq D] in
/-- Bonds of the merged molecule by the underlying darts. -/
theorem bondsBetween_eq (a b : V) : (mergePair M v₁ v₂ hv₁ hne).bondsBetween a b =
    (univ.filter fun x => M.ends x ≠ s(v₁, v₂) ∧ (M.out x = true ∧
      s(mergeMap v₁ v₂ (M.atom x), mergeMap v₁ v₂ (M.atom (M.mate x))) = s(a, b))).card := by
  classical
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter]
  exact card_filter_val (fun x => M.out x = true ∧ s(mergeMap v₁ v₂ (M.atom x), mergeMap v₁ v₂ (M.atom (M.mate x))) = s(a, b))

omit [Fintype D] [DecidableEq D] in
theorem mergeMap_eq_of_ne {u y : V} (hy1 : y ≠ v₁) : mergeMap v₁ v₂ u = y ↔ u = y ∧ y ≠ v₂ := by
  unfold mergeMap
  by_cases h : u = v₂
  · rw [ite_of_pos h]; exact ⟨fun h' => absurd h'.symm hy1, fun h' => absurd (h ▸ h'.1).symm h'.2⟩
  · rw [ite_of_not h]; exact ⟨fun h' => ⟨h', h' ▸ h⟩, fun h' => h'.1⟩

omit [DecidableEq D] in
/-- Bonds away from `v₁, v₂` are unchanged. -/
theorem bondsBetween_far {a b : V} (ha1 : a ≠ v₁) (ha2 : a ≠ v₂) (hb1 : b ≠ v₁) (hb2 : b ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).bondsBetween a b = M.bondsBetween a b := by
  classical
  rw [bondsBetween_eq]
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter]
  congr 1; ext x
  simp only [mem_filter, mem_univ, true_and]
  have key : s(mergeMap v₁ v₂ (M.atom x), mergeMap v₁ v₂ (M.atom (M.mate x))) = s(a, b) ↔ M.ends x = s(a, b) := by
    unfold Molecule.ends
    rw [Sym2.eq_iff, Sym2.eq_iff, mergeMap_eq_of_ne ha1, mergeMap_eq_of_ne hb1, mergeMap_eq_of_ne hb1,
      mergeMap_eq_of_ne ha1]
    tauto
  rw [key]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    rw [h2]; exact sym2_ne_of_left ha1 ha2

/-- Bonds of the merged atom: `bb'(v₁, y) = bb(v₁, y) + bb(v₂, y)`. -/
theorem bondsBetween_v₁ {y : V} (hy1 : y ≠ v₁) (hy2 : y ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).bondsBetween v₁ y = M.bondsBetween v₁ y + M.bondsBetween v₂ y := by
  classical
  rw [bondsBetween_eq]
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter, filter_filter, ← card_union_of_disjoint]
  · congr 1; ext x
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have key : s(mergeMap v₁ v₂ (M.atom x), mergeMap v₁ v₂ (M.atom (M.mate x))) = s(v₁, y) ↔
        M.ends x = s(v₁, y) ∨ M.ends x = s(v₂, y) := by
      unfold Molecule.ends
      rw [Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff, mergeMap_eq_v₁, mergeMap_eq_v₁, mergeMap_eq_of_ne hy1,
        mergeMap_eq_of_ne hy1]
      tauto
    rw [key]
    constructor
    · rintro ⟨_, ho, h | h⟩
      · exact Or.inl ⟨ho, h⟩
      · exact Or.inr ⟨ho, h⟩
    · rintro (⟨ho, h⟩ | ⟨ho, h⟩)
      · exact ⟨by rw [h]; exact sym2_ne_of_right hy1 hy2, ho, Or.inl h⟩
      · exact ⟨by rw [h]; exact sym2_ne_of_right hy1 hy2, ho, Or.inr h⟩
  · rw [disjoint_filter]
    rintro x _ ⟨_, h1⟩ ⟨_, h2⟩
    rw [h1] at h2
    rcases Sym2.eq_iff.mp h2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact hne h
    · exact hy1 h.symm

omit [Fintype D] [DecidableEq D] in
theorem atom_ne_v₂ (x : OffPair M v₁ v₂) : (mergePair M v₁ v₂ hv₁ hne).atom x ≠ v₂ := by
  rw [atom_eq]; unfold mergeMap
  by_cases h : M.atom x.val = v₂
  · rw [ite_of_pos h]; exact hne
  · rw [ite_of_not h]; exact h

omit [DecidableEq D] in
/-- No bond reaches `v₂`. -/
theorem bondsBetween_v₂ (b : V) : (mergePair M v₁ v₂ hv₁ hne).bondsBetween v₂ b = 0 := by
  unfold Molecule.bondsBetween
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ h
  have hm : v₂ ∈ (mergePair M v₁ v₂ hv₁ hne).ends x := by rw [h]; exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp hm with h' | h'
  · exact atom_ne_v₂ x h'.symm
  · exact atom_ne_v₂ _ h'.symm

end Merge

end WaveTurbulence.MoleProp4
