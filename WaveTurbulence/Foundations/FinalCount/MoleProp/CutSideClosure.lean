/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CutConnectivity
import Mathlib.Tactic

/-! # A cut side becomes component-closed when all crossing endpoints are erased -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cut_side_closed_after_erasure (M : Molecule V D) (Y S : Finset V)
    (hcut : ∀ x ∈ Degen.boundaryDarts M S, M.atom (M.mate x) ∈ Y) :
    ∀ a ∈ S, ∀ b, (Degen.eraseAtoms M Y).SameComponent a b → b ∈ S := by
  have hboundary := boundary_erase_eq_empty_of_old_boundary_ends_removed M Y S hcut
  intro a ha b hab
  exact (Degen.sameComponent_mem_iff_of_boundary_empty (Degen.eraseAtoms M Y) S hboundary hab).mp ha

end WaveTurbulence.MoleProp
