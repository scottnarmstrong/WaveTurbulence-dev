/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Bridges
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Two actual parallel bonds remain connected after excluding any one bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem parallel_bonds_path_without (M : Molecule V D) (e : D) {a b : V}
    (hm : 2 ≤ M.bondsBetween a b) :
    Relation.EqvGen (Degen.AdjWithoutBond M e) a b := by
  classical
  let S := M.bonds.filter fun x => M.ends x = s(a,b)
  have hcard : 1 < S.card := by
    change 1 < M.bondsBetween a b
    omega
  let y := if M.out e = true then e else M.mate e
  obtain ⟨x,hx,hxy⟩ := exists_mem_ne hcard y
  have hxout : M.out x = true := (mem_filter.mp (mem_filter.mp hx).1).2
  have hxends : M.ends x = s(a,b) := (mem_filter.mp hx).2
  have hxe : x ≠ e := by
    intro he
    subst x
    have heq : y = e := by simp only [y,hxout,ite_true]
    exact hxy heq.symm
  have hxm : x ≠ M.mate e := by
    intro he
    by_cases ho : M.out e = true
    · have hh := M.out_mate e
      rw [ho] at hh
      rw [he,hh] at hxout
      contradiction
    · exact hxy (by simpa [y,ho] using he)
  rcases Sym2.eq_iff.mp hxends with h | h
  · exact Relation.EqvGen.rel _ _ ⟨x,h.1,h.2,hxe,hxm⟩
  · apply Relation.EqvGen.symm
    exact Relation.EqvGen.rel _ _ ⟨x,h.1,h.2,hxe,hxm⟩

end WaveTurbulence.Mole.AppbAlgorithm
