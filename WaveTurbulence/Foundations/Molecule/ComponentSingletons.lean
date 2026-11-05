/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ComponentDegreeParity
import Mathlib.Tactic

/-! # Actual paths and isolated component sets for the cnblock charge -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem componentSets_path_mem {C : Finset V} (hC : C ∈ Degen.componentSets M)
    {u v : V} (hu : u ∈ C) (hp : M.SameComponent u v) : v ∈ C := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hC
  have h := (Degen.mem_componentSet M a u).mp hu
  have hv : v ∈ M.atoms := (sameComponent_mem_iff M hp).mp h.1
  exact (Degen.mem_componentSet M a v).mpr ⟨hv,sameComponent_trans M h.2 hp⟩

theorem componentSet_eq_singleton_of_degree_zero {v : V} (hv : v ∈ M.atoms)
    (hd : M.deg v = 0) : Degen.componentSet M v = {v} := by
  classical
  have hno : ∀ z, ¬ M.Adj v z := by
    rintro z ⟨x,hx,_hz⟩
    have hempty : M.dartsAt v = ∅ := Finset.card_eq_zero.mp hd
    have hmem := (mem_dartsAt M v x).mpr hx
    rw [hempty] at hmem
    exact Finset.notMem_empty x hmem
  have hpath : ∀ u z, M.SameComponent u z → (u = v ↔ z = v) := by
    intro u z hp
    induction hp with
    | rel u z huz =>
      constructor
      · intro hu
        exact (hno z (hu ▸ huz)).elim
      · intro hz
        exact (hno u (hz ▸ adj_symmetric M huz)).elim
    | refl u => rfl
    | symm u z hp ih => exact ih.symm
    | trans u z y h1 h2 ih1 ih2 => exact ih1.trans ih2
  ext z
  rw [Degen.mem_componentSet,Finset.mem_singleton]
  constructor
  · rintro ⟨_hz,hp⟩
    exact (hpath v z hp).mp rfl
  · rintro rfl
    exact ⟨hv,sameComponent_refl M _⟩

end WaveTurbulence.Mole
