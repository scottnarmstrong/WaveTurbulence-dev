/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # A connected block with a double bond at its joints is that bond -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The two rung incidences in a full four-incidence row are distinct. -/
@[expose] def FourIncidences.rung {M : Molecule V D} {x y p q : V}
    (R : FourIncidences M x ![y,y,p,q]) : TwoIncidences M x y where
  dart := fun i => R.dart ⟨i.1,by omega⟩
  injective := by
    intro i j he
    have hh := R.injective he
    exact Fin.ext (congrArg (fun z : Fin 4 => z.1) hh)
  atom_eq := fun i => R.atom_eq _
  neighbor_eq := by intro i; fin_cases i <;> exact R.neighbor_eq _

/-- Two internal incidences exhaust a degree-two joint. -/
theorem twoIncidences_internal_image (M : Molecule V D) {S : Finset V} {x y : V}
    (R : TwoIncidences M x y) (hx : x ∈ S) (hy : y ∈ S) (hd : M.degIn S x=2) :
    univ.image R.dart=(M.dartsAt x).filter (M.InGroup S) := by
  have hs : univ.image R.dart ⊆ (M.dartsAt x).filter (M.InGroup S) := by
    intro z hz
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M x _).mpr (R.atom_eq i),
      (R.atom_eq i).symm ▸ hx,(R.neighbor_eq i).symm ▸ hy⟩
  apply eq_of_subset_of_card_le hs
  rw [card_image_of_injective _ R.injective,card_univ,Fintype.card_fin]
  exact hd.le

/-- A degree-two joint carrying the double pair has no other neighbor inside S. -/
theorem twoIncidences_unique_internal_neighbor (M : Molecule V D) {S : Finset V} {x y z : V}
    (R : TwoIncidences M x y) (hx : x ∈ S) (hy : y ∈ S) (hd : M.degIn S x=2)
    (ha : (Mole.induced M S).Adj x z) : z=y := by
  obtain ⟨d,hdx,hdz⟩ := ha
  have hmem : d.1 ∈ (M.dartsAt x).filter (M.InGroup S) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M x d.1).mpr hdx,d.2⟩
  rw [← twoIncidences_internal_image M R hx hy hd] at hmem
  obtain ⟨i,_hi,he⟩ := mem_image.mp hmem
  have hn := R.neighbor_eq i
  rw [he] at hn
  exact hdz.symm.trans hn

/-- TARGET subsetvc, elementary double-bond case: if the two joints of a
connected block already share two incidences, they exhaust that block. -/
theorem connected_block_eq_double_pair (M : Molecule V D) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) (hC : GroupConnected M S) (R : TwoIncidences M a b) : S={a,b} := by
  obtain ⟨ha,hb⟩ := Mole.block_joint_degrees M hB
  have close {u z : V} (hu : u ∈ ({a,b} : Finset V))
      (hz : (Mole.induced M S).Adj u z) : z ∈ ({a,b} : Finset V) := by
    rcases mem_insert.mp hu with rfl | hu
    · rw [twoIncidences_unique_internal_neighbor M R hB.2.1 hB.2.2.1 ha hz]
      exact mem_insert_of_mem (mem_singleton_self b)
    · have he : u=b := mem_singleton.mp hu
      subst u
      rw [twoIncidences_unique_internal_neighbor M R.mates hB.2.2.1 hB.2.1 hb hz]
      exact mem_insert_self _ _
  have stable {u v : V} (hp : (Mole.induced M S).SameComponent u v) :
      u ∈ ({a,b} : Finset V) ↔ v ∈ ({a,b} : Finset V) := by
    induction hp with
    | rel u v huv => exact ⟨fun hu => close hu huv,fun hv => close hv (Mole.adj_symmetric _ huv)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  apply subset_antisymm
  · intro v hv
    exact (stable (hC a hB.2.1 v hv)).mp (mem_insert_self _ _)
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hB.2.1
    · have he : v=b := mem_singleton.mp hv
      subst v
      exact hB.2.2.1

end WaveTurbulence.Vine
