/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionComponentEquiv
import Mathlib.Tactic

/-! # A connected deletion with one boundary dart preserves component count -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem numComponents_erase_single_boundary (M : Molecule V D) (Y : Finset V)
    (hcard : (Degen.boundaryDarts M Y).card = 1)
    (hY : ∀ a ∈ Y,∀ b ∈ Y,M.SameComponent a b) :
    (Degen.eraseAtoms M Y).numComponents = M.numComponents := by
  classical
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (Degen.boundaryDarts M Y).card by omega)
  have hx' := (mem_filter.mp hx).2
  apply numComponents_eraseAtoms_eq_of_cut_paths M Y (M.atom (M.mate x))
    (mem_sdiff.mpr ⟨M.atom_mem _,hx'.2⟩)
  · intro a ha
    exact Relation.EqvGen.trans _ _ _ (hY a ha _ hx'.1) (Relation.EqvGen.rel _ _ ⟨x,rfl,rfl⟩)
  · intro y hy
    have he : y = x := card_le_one.mp hcard.le y hy x hx
    rw [he]
    exact Relation.EqvGen.refl _

end WaveTurbulence.Mole.AppbAlgorithm
