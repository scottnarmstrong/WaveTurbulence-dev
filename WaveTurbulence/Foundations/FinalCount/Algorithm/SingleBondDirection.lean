/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PairBondEnumeration
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Reading a single bond's direction from its outgoing representative -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem directed_iff_outgoing_atom (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hm : M.bondsBetween a b = 1) {x : D} (hout : M.out x = true)
    (hend : M.ends x = s(a,b)) : M.Directed a b ↔ M.atom x = a := by
  classical
  constructor
  · rintro ⟨y,hy,hya,hyb⟩
    have hc : (parallelBonds M a b).card ≤ 1 := by change M.bondsBetween a b ≤ 1; omega
    have hx : x ∈ parallelBonds M a b := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hout⟩,hend⟩
    have hy' : y ∈ parallelBonds M a b := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hy⟩,
      by simp only [Molecule.ends,hya,hyb]⟩
    have he := card_le_one.mp hc x hx y hy'
    exact he ▸ hya
  · intro ha
    rcases Sym2.eq_iff.mp hend with h | h
    · exact ⟨x,hout,h⟩
    · exact (hab (ha.symm.trans h.1)).elim

theorem directed_reverse_iff_outgoing_atom_ne (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hm : M.bondsBetween a b = 1) {x : D} (hout : M.out x = true)
    (hend : M.ends x = s(a,b)) : M.Directed b a ↔ M.atom x ≠ a := by
  have hm' : M.bondsBetween b a = 1 := (bondsBetween_symm M b a).trans hm
  rw [directed_iff_outgoing_atom M hab.symm hm' hout (hend.trans Sym2.eq_swap)]
  rcases Sym2.eq_iff.mp hend with h | h
  · rw [h.1]
    simp [hab]
  · rw [h.1]
    simp [hab.symm]

end WaveTurbulence.Mole.AppbAlgorithm
