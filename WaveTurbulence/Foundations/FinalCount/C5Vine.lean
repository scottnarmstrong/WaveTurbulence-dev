/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Fold
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.VineIIHalf
import Mathlib.Tactic

/-! # Prop 9.6, case (5): the half-closure of vine (II) has a triple bond -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem mem_groupBonds_atoms {N : Molecule V D} {e : Sym2 V} (he : e ∈ N.groupBonds N.atoms) :
    ∃ a ∈ N.atoms, ∃ b ∈ N.atoms, e = s(a, b) := by
  unfold Molecule.groupBonds at he
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp he
  have := (Finset.mem_filter.mp (Finset.mem_val.mp hx)).2
  exact ⟨N.atom x, this.2.1, N.atom (N.mate x), this.2.2, rfl⟩

/-- The triple bond of a half-closure of vine (II), in terms of the data. -/
theorem triple_of_data {N : Molecule V D} {k : ℕ} {f : V → ℕ} (hinj : Set.InjOn f ↑N.atoms)
    (himg : N.atoms.image f = Finset.range (4 + 2 * k) \ {0, 1})
    (hbonds : (N.groupBonds N.atoms).map (Sym2.map f) = halfClosureIIBonds k) :
    ∃ p ∈ N.atoms, ∃ q ∈ N.atoms, f p = 2 ∧ f q = 3 ∧ 3 ≤ N.bondsBetween p q := by
  classical
  have h2 : (2 : ℕ) ∈ N.atoms.image f := by rw [himg]; simp; omega
  have h3 : (3 : ℕ) ∈ N.atoms.image f := by rw [himg]; simp; omega
  obtain ⟨p, hp, hfp⟩ := mem_image.mp h2
  obtain ⟨q, hq, hfq⟩ := mem_image.mp h3
  refine ⟨p, hp, q, hq, hfp, hfq, ?_⟩
  have hcount : 3 ≤ Multiset.count s(2, 3) (halfClosureIIBonds k) := by
    rw [halfClosureIIBonds_eq]
    unfold ladderBonds
    rw [Multiset.count_add]
    have : Multiset.count s(2, 3) (3 • ({s(2, 3)} : Multiset (Sym2 ℕ))) = 3 := by simp
    omega
  rw [← hbonds, Multiset.count_map] at hcount
  have hfilt : (N.groupBonds N.atoms).filter (fun e => s(2, 3) = Sym2.map f e) =
      (N.groupBonds N.atoms).filter (fun e => s(p, q) = e) := by
    refine Multiset.filter_congr fun e he => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_groupBonds_atoms he
    simp only [Sym2.map_mk]
    constructor
    · intro hh
      rcases Sym2.eq_iff.mp hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : p = a := hinj hp ha (by rw [hfp, h1])
        have e2 : q = b := hinj hq hb (by rw [hfq, h2])
        rw [e1, e2]
      · have e1 : q = a := hinj hq ha (by rw [hfq, h2])
        have e2 : p = b := hinj hp hb (by rw [hfp, h1])
        rw [e1, e2, Sym2.eq_swap]
    · intro hh
      rcases Sym2.eq_iff.mp hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hfp, hfq]
      · rw [← h1, ← h2, hfp, hfq, Sym2.eq_swap]
  rw [hfilt] at hcount
  have : Multiset.card ((N.groupBonds N.atoms).filter (fun e => s(p, q) = e)) =
      Multiset.count s(p, q) (N.groupBonds N.atoms) := by
    rw [Multiset.count_eq_card_filter_eq]
  rw [this] at hcount
  have hc := count_groupBonds_atoms N p q
  omega

/-- A half-closure of vine (II) has a triple bond between two atoms. -/
theorem halfClosure_triple {N : Molecule V D} (h : IsVineIIHalfClosure N) :
    ∃ p ∈ N.atoms, ∃ q ∈ N.atoms, 3 ≤ N.bondsBetween p q := by
  obtain ⟨k, f, hinj, himg, hbonds⟩ := h
  obtain ⟨p, hp, q, hq, _, _, h3⟩ := triple_of_data hinj himg hbonds
  exact ⟨p, hp, q, hq, h3⟩

end
end WaveTurbulence.FinalCountG8
