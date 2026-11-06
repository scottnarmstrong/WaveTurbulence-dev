/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeComponentPartitions
import Mathlib.Tactic

/-! # Reattaching a joint to an actual connected component -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] (M : Molecule V D)

/-- A connected group remains connected after adjoining an adjacent atom. -/
theorem connected_insert_of_adj {P : Finset V} {v x : V} (hc : GroupConnected M P)
    (hx : x ∈ P) (hadj : M.Adj v x) : GroupConnected M (insert v P) := by
  have hanchor : ∀ u ∈ insert v P, (induced M (insert v P)).SameComponent u x := by
    intro u hu
    rcases Finset.mem_insert.mp hu with he | huP
    · subst u
      apply Relation.EqvGen.rel
      exact (induced_adj_iff M (insert v P) v x).mpr
        ⟨hadj,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem hx⟩
    · exact induced_path_mono M (Finset.subset_insert v P) (hc.2 u huP x hx)
  refine ⟨Finset.insert_nonempty _ _,?_⟩
  intro u hu z hz
  exact sameComponent_trans (induced M (insert v P)) (hanchor u hu)
    (sameComponent_symm (induced M (insert v P)) (hanchor z hz))

/-- Reattaching a deleted atom through one actual edge restores connectedness. -/
theorem connected_of_erase_and_adj {S : Finset V} {v : V} (hv : v ∈ S)
    (hc : GroupConnected M (S.erase v)) (ha : ∃ x ∈ S.erase v, M.Adj v x) : GroupConnected M S := by
  obtain ⟨x,hx,hadj⟩ := ha
  have hh := connected_insert_of_adj M hc hx hadj
  rw [Finset.insert_erase hv] at hh
  exact hh

variable [Fintype D]

/-- A positive-degree loop-free joint attaches to its deleted connected
component through an actual surviving bond. -/
theorem connected_of_erase_and_positive_degree {S : Finset V} {v : V} (hv : v ∈ S)
    (hc : GroupConnected M (S.erase v)) (hd : 0 < M.degIn S v)
    (hno : ∀ x, M.atom x = v → M.atom (M.mate x) ≠ v) : GroupConnected M S := by
  apply connected_of_erase_and_adj M hv hc
  have hcard : 0 < ((M.dartsAt v).filter (M.InGroup S)).card := hd
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hcard
  obtain ⟨hxv,hxg⟩ := Finset.mem_filter.mp hx
  have hxa := (mem_dartsAt M v x).mp hxv
  exact ⟨M.atom (M.mate x),Finset.mem_erase.mpr ⟨hno x hxa,hxg.2⟩,⟨x,hxa,rfl⟩⟩

end WaveTurbulence.Mole
