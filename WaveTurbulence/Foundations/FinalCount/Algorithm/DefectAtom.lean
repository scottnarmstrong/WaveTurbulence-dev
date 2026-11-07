/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # A nontrivial molecule has a nonisolated atom of degree below four -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eq_of_sameComponent_of_degree_zero (M : Molecule V D) {a b : V}
    (hp : M.SameComponent a b) (hb : M.deg b = 0) : a = b := by
  have hno : ∀ u,¬M.Adj u b := by
    rintro u ⟨x,hx,hy⟩
    have hm : M.mate x ∈ M.dartsAt b := mem_filter.mpr ⟨mem_univ _,hy⟩
    have hh : 0 < M.deg b := card_pos.mpr ⟨M.mate x,hm⟩
    omega
  have hsep : ∀ u v,M.Adj u v → (u = b ↔ v = b) := by
    intro u v huv
    constructor
    · intro he
      subst u
      exact (hno v (adj_symmetric M huv)).elim
    · intro he
      subst v
      exact (hno u huv).elim
  have hm : ∀ u v,M.SameComponent u v → (u = b ↔ v = b) := by
    intro u v h
    induction h with
    | rel u v h => exact hsep u v h
    | refl u => rfl
    | symm u v h ih => exact ih.symm
    | trans u v w h h' ih ih' => exact ih.trans ih'
  exact (hm a b hp).mpr rfl

theorem exists_nonisolated_defect (M : Molecule V D) (hM : M.IsMolecule)
    (hne : M.bonds.Nonempty) : ∃ v ∈ M.atoms,1 ≤ M.deg v ∧ M.deg v ≤ 3 := by
  obtain ⟨e,he⟩ := hne
  obtain ⟨v,hv,hpath,hdefect⟩ := hM.2 (M.atom e) (M.atom_mem e)
  have hpos : 0 < M.deg v := by
    by_contra hn
    have hz : M.deg v = 0 := by omega
    have hEq := eq_of_sameComponent_of_degree_zero M hpath hz
    have hd : 0 < M.deg (M.atom e) := card_pos.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
    rw [hEq,hz] at hd
    omega
  have hcap := deg_le_four M hM hv
  exact ⟨v,hv,by omega,by omega⟩

end WaveTurbulence.Mole.AppbAlgorithm
