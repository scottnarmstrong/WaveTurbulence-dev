/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitDeletion
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Even-degree components and the degree-two degenerate reduction -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact cut handshaking, counting every internal loop twice. -/
theorem sum_degrees_cut (M : Molecule V D) (S : Finset V) :
    (∑ z ∈ S, M.deg z) = 2 * (M.groupBonds S).card + (boundaryDarts M S).card := by
  classical
  let A := univ.filter (fun x : D => M.atom x ∈ S)
  have hf := sum_fiberwise_of_maps_to (s := A) (t := S) (g := M.atom)
    (fun x hx => (mem_filter.mp hx).2) (fun _ => (1 : ℕ))
  have hflat : (∑ z ∈ S, M.deg z) = A.card := by
    rw [← show (∑ _x ∈ A, (1 : ℕ)) = A.card by simp]
    rw [← hf]
    apply sum_congr rfl
    intro z hz
    have he : A.filter (fun x => M.atom x = z) = M.dartsAt z := by
      ext x
      simp only [A, Molecule.dartsAt, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨hx.symm ▸ hz, hx⟩
    rw [he]
    simp only [sum_const, smul_eq_mul, mul_one, Molecule.deg]
  have hpartition : A.card = (internalDarts M S).card + (boundaryDarts M S).card := by
    have hh := card_filter_add_card_filter_not (s := A) (fun x => M.atom (M.mate x) ∈ S)
    simpa only [A, filter_filter, internalDarts, boundaryDarts] using hh.symm
  have hcard : Fintype.card {x : D // M.InGroup S x} = (internalDarts M S).card := by
    rw [Fintype.card_subtype]
    rfl
  have htw := Mole.two_mul_card_bonds (Mole.induced M S)
  rw [Mole.induced_card_bonds, hcard] at htw
  rw [hflat, hpartition, ← htw]

/-- A finite cut in an even-degree component cannot consist of one bond. -/
theorem boundary_card_ne_one_of_even_degrees (M : Molecule V D)
    (heven : ∀ z ∈ M.atoms, Even (M.deg z)) (S : Finset V) (hS : S ⊆ M.atoms) :
    (boundaryDarts M S).card ≠ 1 := by
  have hs : (∑ z ∈ S, M.deg z) = 2 * ∑ z ∈ S, M.deg z / 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    obtain ⟨k, hk⟩ := heven z (hS hz)
    omega
  have hcut := sum_degrees_cut M S
  omega

/-- Removing a degree-two atom from the original all-even molecule loses
at least one circuit. This gives DH23 10.5(2)'s fixed-label power gain. -/
theorem circuitRank_erase_two_le_sub_one_of_even (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    (heven : ∀ z ∈ M.atoms, Even (M.deg z)) {v : V} (hv : v ∈ M.atoms) (htwo : M.deg v = 2) :
    (eraseAtoms M {v}).circuitRank ≤ M.circuitRank - 1 := by
  have hn : ∀ S ∈ newComponents M {v}, (boundaryDarts M S).card ≠ 1 := by
    intro S hS
    obtain ⟨hS, _⟩ := mem_filter.mp hS
    obtain ⟨u, _, rfl⟩ := mem_image.mp hS
    apply boundary_card_ne_one_of_even_degrees M heven
    intro z hz
    exact ((mem_residualComponent M {v} u z).mp hz).1
  have hc := two_mul_card_newComponents_le_of_no_single M {v} hn
  have hb := card_boundary_add_twice_self_eq_deg M v
  have hi := card_incident_add_self_eq_deg M v
  have hd := circuitRank_erase_singleton_sub M hconn hv
  omega

end WaveTurbulence.Degen
