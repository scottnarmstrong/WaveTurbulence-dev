/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
import Mathlib.Tactic

/-! # The designated representatives of two actual components are separated -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_induced_atoms_path (M : Molecule V D) {a b : V} (hp : M.SameComponent a b) :
    (induced M M.atoms).SameComponent a b := by
  induction hp with
  | rel u v h =>
    obtain ⟨x,hx,hy⟩ := h
    apply Relation.EqvGen.rel
    apply (induced_adj_iff M M.atoms u v).mpr
    exact ⟨⟨x,hx,hy⟩,hx ▸ M.atom_mem x,hy ▸ M.atom_mem (M.mate x)⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm u v h ih => exact ih.symm
  | trans u v w h h' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem appb_twoComponents_not_sameComponent (M : Molecule V D) {a b : V}
    (h : TwoComponents M M.atoms a b) : ¬M.SameComponent a b := by
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  intro hp
  have hside := partition_path_side M hcover hno (appb_induced_atoms_path M hp)
  exact disjoint_left.mp hdis (hside.mp ha) hb

end WaveTurbulence.Mole
