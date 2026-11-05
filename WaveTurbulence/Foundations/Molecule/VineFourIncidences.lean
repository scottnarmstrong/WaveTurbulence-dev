/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineJointIndicators
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Four distinct incidences exhaust a molecule atom (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Four actual distinct darts at an atom, with recorded neighboring atoms.
Repeated neighbors are allowed; repeated darts are not. -/
structure FourIncidences (M : Molecule V D) (v : V) (neighbors : Fin 4 → V) where
  dart : Fin 4 → D
  injective : Function.Injective dart
  atom_eq : ∀ i,M.atom (dart i)=v
  neighbor_eq : ∀ i,M.atom (M.mate (dart i))=neighbors i

/-- In a molecule of degree at most four, the four recorded incidences are
all the atom's darts, including any repeated bond endpoints. -/
theorem fourIncidences_image (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} {neighbors : Fin 4 → V} (R : FourIncidences M v neighbors) :
    univ.image R.dart=M.dartsAt v := by
  have hsub : univ.image R.dart ⊆ M.dartsAt v := by
    intro x hx
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hx
    exact (Mole.mem_dartsAt M v _).mpr (R.atom_eq i)
  apply eq_of_subset_of_card_le hsub
  rw [card_image_of_injective _ R.injective]
  have hv : v ∈ M.atoms := R.atom_eq 0 ▸ M.atom_mem (R.dart 0)
  simpa only [card_univ,Fintype.card_fin,Molecule.deg] using Mole.deg_le_four M hM hv

/-- The degree inside a selected group is the sum of the four actual
neighbor membership indicators. -/
theorem fourIncidences_degree (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} {neighbors : Fin 4 → V} (R : FourIncidences M v neighbors)
    (S : Finset V) (hv : v ∈ S) :
    M.degIn S v=∑ i : Fin 4,jointIndicator S (neighbors i) := by
  unfold Molecule.degIn
  rw [← fourIncidences_image M hM R,filter_image,card_image_of_injective _ R.injective]
  have hpred (i : Fin 4) : M.InGroup S (R.dart i) ↔ neighbors i ∈ S := by
    simp only [Molecule.InGroup,R.atom_eq,R.neighbor_eq,hv,true_and]
  simp only [hpred,jointIndicator,sum_boole,Nat.cast_id]

end WaveTurbulence.Vine
