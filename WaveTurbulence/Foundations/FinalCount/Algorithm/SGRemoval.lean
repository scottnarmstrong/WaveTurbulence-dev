/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGPost
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGDeletionGraph
import Mathlib.Tactic

/-! # A realization of the removal of the exceptional atoms and its numerical data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem exists_removal (M : Molecule V D) (hM : M.IsMolecule) (S : Finset V) (hS : S ⊆ M.atoms)
    (hne : M.atoms.Nonempty) :
    ∃ P : AppbPattern, ∃ r : AppbRealization M P, r.removedAtoms = S ∧
      P.edges.length ≤ 8*S.card ∧ P.removed.card+P.vertices.card ≤ 18*S.card := by
  let v0 : M.atoms := ⟨hne.choose,hne.choose_spec⟩
  let e := (Fintype.equivFin {x // x ∈ appbRemovedBonds M S}).symm
  refine ⟨appbEncodedRemovalPattern M S hS e,appbEncodedRemoval M S hS v0 e,
    appb_encoded_removed_eq M S hS v0 e,?_⟩
  have hlen := appb_encoded_edges_length M S hS e
  have hm : Fintype.card {x // x ∈ appbRemovedBonds M S} ≤ 8*S.card := by
    rw [Fintype.card_coe]
    exact card_removedBonds_le M hM S hS
  have hrem : (appbEncodedRemovalPattern M S hS e).removed.card ≤ S.card :=
    card_image_le.trans (by simp)
  have hv := AppbPattern.card_vertices_le (appbEncodedRemovalPattern M S hS e)
  rw [hlen] at hv ⊢
  exact ⟨hm,by omega⟩

end WaveTurbulence.Mole.AppbAlgorithm
