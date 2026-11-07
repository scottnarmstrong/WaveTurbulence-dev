/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBEncodedRemoval
import Mathlib.Tactic

/-! # Exact atom set and edge coordinates of an encoded actual removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_encoded_removed_eq (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (v0 : M.atoms) {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    (appbEncodedRemoval M Y hY v0 e).removedAtoms = Y :=
  appb_encoded_removed_atoms M Y hY v0 e

theorem appb_encoded_vertex_code (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (v0 v : M.atoms) {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) :
    (appbEncodedRemoval M Y hY v0 e).vertex (appbAtomCode M v) = v.val :=
  congrArg Subtype.val (appb_decode_atom_code M v0 v)

theorem appb_encoded_edge_val (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (v0 : M.atoms) {m : ℕ} (e : Fin m ≃ {x // x ∈ appbRemovedBonds M Y}) (j : Fin m) :
    ((appbEncodedRemoval M Y hY v0 e).edge ((finCongr (appb_encoded_edges_length M Y hY e)).symm j)).val =
      (e j).val := by
  change (e ((finCongr (appb_encoded_edges_length M Y hY e))
    ((finCongr (appb_encoded_edges_length M Y hY e)).symm j))).val = _
  rw [Equiv.apply_symm_apply]

end WaveTurbulence.Mole
