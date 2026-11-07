/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideCircuitRank
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAtoms
import Mathlib.Tactic

/-! # A strict size measure compatible with component recursion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def State.mass (s : State.{u,v} V) : ℕ := s.bondPotential+s.atomPotential

theorem GeometricStep.atomPotential_le {s t : State.{u,v} V} (h : GeometricStep s t) :
    t.atomPotential ≤ s.atomPotential := by
  cases h with
  | bridge e => exact le_refl _
  | delete k r => have hh := r.post_card_atoms; change r.post.atoms.card ≤ s.graph.atoms.card; omega
  | common r => have hh := r.post_card_atoms; change r.post.atoms.card ≤ s.graph.atoms.card; omega
  | reinsertS33 r =>
    change (r.directedPostWithBond 3 5 ⟨1,by decide⟩).atoms.card ≤ s.graph.atoms.card
    rw [r.directedPostWithBond_atoms 3 5 ⟨1,by decide⟩ (by decide) (by decide) (by decide) (by decide)]
    exact Finset.card_le_card Finset.sdiff_subset
  | reinsertD33 r =>
    change (r.directedPostWithBond 3 4 ⟨2,by decide⟩).atoms.card ≤ s.graph.atoms.card
    rw [r.directedPostWithBond_atoms 3 4 ⟨2,by decide⟩ (by decide) (by decide) (by decide) (by decide)]
    exact Finset.card_le_card Finset.sdiff_subset
  | r32 r t =>
    have h1 := r.post_card_atoms
    have h2 := t.post_card_atoms
    change t.post.atoms.card ≤ s.graph.atoms.card
    omega

theorem GeometricStep.mass_lt {s t : State.{u,v} V} (h : GeometricStep s t) : t.mass < s.mass := by
  have he := h.bondPotential_lt
  have hv := h.atomPotential_le
  unfold State.mass
  omega

theorem mass_closed_side_add (s : State.{u,v} V) (S : Finset V) (hS : AppbClosedSide s.graph S) :
    s.mass = (ofMolecule (appbSideMolecule s.graph S hS)).mass+
      (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)).mass := by
  have he := bonds_card_closed_side_add s.graph S hS
  have hv := atoms_card_closed_side_add s.graph S hS
  change s.graph.bonds.card+s.graph.atoms.card = _
  change s.graph.bonds.card+s.graph.atoms.card =
    ((appbSideMolecule s.graph S hS).bonds.card+(appbSideMolecule s.graph S hS).atoms.card)+
    ((appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement).bonds.card+
      (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement).atoms.card)
  omega

end WaveTurbulence.Mole.AppbAlgorithm
