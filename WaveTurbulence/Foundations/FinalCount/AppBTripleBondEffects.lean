/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentEffects
import Mathlib.Tactic

/-! # DH23 triple-bond operation graph effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A boundary-free nonempty deleted set exhausts its connected component. -/
theorem post_atoms_empty_of_boundary_zero
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty) (hb : P.boundaryCount = 0) : r.post.atoms = ∅ := by
  have hzero : Degen.boundaryDarts M r.removedAtoms = ∅ := by
    apply card_eq_zero.mp
    rw [r.boundary_card,hb]
  obtain ⟨a,ha⟩ := hne
  have haY : r.vertex a ∈ r.removedAtoms := mem_image_of_mem _ ha
  have haM : r.vertex a ∈ M.atoms := r.removedAtoms_subset haY
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvM,hvY⟩ := mem_sdiff.mp hv
  have hp := hconn (r.vertex a) haM v hvM
  exact hvY ((Degen.sameComponent_mem_iff_of_boundary_empty M _ hzero hp).mp haY)

end AppbRealization

end WaveTurbulence.Mole
